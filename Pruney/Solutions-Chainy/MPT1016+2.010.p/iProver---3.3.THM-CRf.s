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
% DateTime   : Thu Dec  3 12:06:53 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  188 (7762 expanded)
%              Number of clauses        :  127 (2061 expanded)
%              Number of leaves         :   16 (1571 expanded)
%              Depth                    :   25
%              Number of atoms          :  674 (58718 expanded)
%              Number of equality atoms :  298 (18621 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f48,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f35,f34])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_399,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_400,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_2675,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_401,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2874,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2875,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2874])).

cnf(c_3497,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2675,c_27,c_401,c_2875])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_345,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_24,c_22])).

cnf(c_2094,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_349])).

cnf(c_2678,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_3503,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_2678])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2684,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2093,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_349])).

cnf(c_2679,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2093])).

cnf(c_3247,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_2679])).

cnf(c_3504,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_3247])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_56,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_58,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_59,plain,
    ( sK1(X0) != sK0(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_61,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2963,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2964,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_2682,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2688,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3542,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2682,c_2688])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3735,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3542,c_2689])).

cnf(c_4001,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3735,c_27])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4006,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_2691])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_373,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_374,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_2677,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_375,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_3879,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2677,c_27,c_375,c_2875])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_239,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_191])).

cnf(c_2681,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_4208,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3879,c_2681])).

cnf(c_4556,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4006,c_4208])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_386,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_387,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_2676,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_388,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_3427,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2676,c_27,c_388,c_2875])).

cnf(c_4209,plain,
    ( r2_hidden(sK1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_2681])).

cnf(c_4567,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4006,c_4209])).

cnf(c_4691,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_25,c_27,c_58,c_61,c_2875,c_2964,c_3247,c_4556,c_4567])).

cnf(c_4697,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3503,c_4691])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_73,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_412,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_413,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_653,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_413,c_17])).

cnf(c_744,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_400,c_17])).

cnf(c_835,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_387,c_17])).

cnf(c_926,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_374,c_17])).

cnf(c_2104,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_2116,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_2092,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_426])).

cnf(c_2097,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2966,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_3079,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_2091,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_426])).

cnf(c_4455,plain,
    ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_4457,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_4455])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2686,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3507,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3497,c_2686])).

cnf(c_2683,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3742,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3507,c_2683])).

cnf(c_3893,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3742])).

cnf(c_4775,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3893,c_25,c_27,c_58,c_61,c_2875,c_2964,c_4556,c_4567])).

cnf(c_4777,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4775])).

cnf(c_4780,plain,
    ( sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4775,c_2678])).

cnf(c_4784,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_4775,c_2686])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2685,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3246,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_2679])).

cnf(c_3505,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_3246])).

cnf(c_4699,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3505,c_25,c_27,c_58,c_61,c_2875,c_2964,c_3246,c_4556,c_4567])).

cnf(c_4796,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_4784,c_4699])).

cnf(c_5147,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4780,c_4796])).

cnf(c_5148,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4780,c_4691])).

cnf(c_5644,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_5147,c_5148])).

cnf(c_5646,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4697,c_22,c_73,c_77,c_653,c_744,c_835,c_926,c_2116,c_2092,c_2874,c_3079,c_4457,c_4777,c_5644])).

cnf(c_5661,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5646,c_2685])).

cnf(c_5837,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5661,c_25,c_27,c_58,c_61,c_2875,c_2964,c_4556,c_4567])).

cnf(c_5658,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_5646,c_2679])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_242,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_191])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_242])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_2913,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_2915,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2913])).

cnf(c_2914,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2919,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_6315,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5658,c_2915,c_2919])).

cnf(c_6322,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5837,c_6315])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.66/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/1.00  
% 2.66/1.00  ------  iProver source info
% 2.66/1.00  
% 2.66/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.66/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/1.00  git: non_committed_changes: false
% 2.66/1.00  git: last_make_outside_of_git: false
% 2.66/1.00  
% 2.66/1.00  ------ 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options
% 2.66/1.00  
% 2.66/1.00  --out_options                           all
% 2.66/1.00  --tptp_safe_out                         true
% 2.66/1.00  --problem_path                          ""
% 2.66/1.00  --include_path                          ""
% 2.66/1.00  --clausifier                            res/vclausify_rel
% 2.66/1.00  --clausifier_options                    --mode clausify
% 2.66/1.00  --stdin                                 false
% 2.66/1.00  --stats_out                             all
% 2.66/1.00  
% 2.66/1.00  ------ General Options
% 2.66/1.00  
% 2.66/1.00  --fof                                   false
% 2.66/1.00  --time_out_real                         305.
% 2.66/1.00  --time_out_virtual                      -1.
% 2.66/1.00  --symbol_type_check                     false
% 2.66/1.00  --clausify_out                          false
% 2.66/1.00  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     num_symb
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       true
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  ------ Parsing...
% 2.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.00  ------ Proving...
% 2.66/1.00  ------ Problem Properties 
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  clauses                                 23
% 2.66/1.00  conjectures                             6
% 2.66/1.00  EPR                                     9
% 2.66/1.00  Horn                                    18
% 2.66/1.00  unary                                   2
% 2.66/1.00  binary                                  10
% 2.66/1.00  lits                                    59
% 2.66/1.00  lits eq                                 12
% 2.66/1.00  fd_pure                                 0
% 2.66/1.00  fd_pseudo                               0
% 2.66/1.00  fd_cond                                 0
% 2.66/1.00  fd_pseudo_cond                          3
% 2.66/1.00  AC symbols                              0
% 2.66/1.00  
% 2.66/1.00  ------ Schedule dynamic 5 is on 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ 
% 2.66/1.00  Current options:
% 2.66/1.00  ------ 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options
% 2.66/1.00  
% 2.66/1.00  --out_options                           all
% 2.66/1.00  --tptp_safe_out                         true
% 2.66/1.00  --problem_path                          ""
% 2.66/1.00  --include_path                          ""
% 2.66/1.00  --clausifier                            res/vclausify_rel
% 2.66/1.00  --clausifier_options                    --mode clausify
% 2.66/1.00  --stdin                                 false
% 2.66/1.00  --stats_out                             all
% 2.66/1.00  
% 2.66/1.00  ------ General Options
% 2.66/1.00  
% 2.66/1.00  --fof                                   false
% 2.66/1.00  --time_out_real                         305.
% 2.66/1.00  --time_out_virtual                      -1.
% 2.66/1.00  --symbol_type_check                     false
% 2.66/1.00  --clausify_out                          false
% 2.66/1.00  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     none
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       false
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ Proving...
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS status Theorem for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00   Resolution empty clause
% 2.66/1.00  
% 2.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  fof(f6,axiom,(
% 2.66/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f15,plain,(
% 2.66/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/1.00    inference(ennf_transformation,[],[f6])).
% 2.66/1.00  
% 2.66/1.00  fof(f16,plain,(
% 2.66/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(flattening,[],[f15])).
% 2.66/1.00  
% 2.66/1.00  fof(f27,plain,(
% 2.66/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(nnf_transformation,[],[f16])).
% 2.66/1.00  
% 2.66/1.00  fof(f28,plain,(
% 2.66/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(rectify,[],[f27])).
% 2.66/1.00  
% 2.66/1.00  fof(f29,plain,(
% 2.66/1.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f30,plain,(
% 2.66/1.00    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 2.66/1.00  
% 2.66/1.00  fof(f48,plain,(
% 2.66/1.00    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f11,conjecture,(
% 2.66/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f12,negated_conjecture,(
% 2.66/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.66/1.00    inference(negated_conjecture,[],[f11])).
% 2.66/1.00  
% 2.66/1.00  fof(f22,plain,(
% 2.66/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.66/1.00    inference(ennf_transformation,[],[f12])).
% 2.66/1.00  
% 2.66/1.00  fof(f23,plain,(
% 2.66/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.66/1.00    inference(flattening,[],[f22])).
% 2.66/1.00  
% 2.66/1.00  fof(f31,plain,(
% 2.66/1.00    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.66/1.00    inference(nnf_transformation,[],[f23])).
% 2.66/1.00  
% 2.66/1.00  fof(f32,plain,(
% 2.66/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.66/1.00    inference(flattening,[],[f31])).
% 2.66/1.00  
% 2.66/1.00  fof(f33,plain,(
% 2.66/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.66/1.00    inference(rectify,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f35,plain,(
% 2.66/1.00    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f34,plain,(
% 2.66/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f36,plain,(
% 2.66/1.00    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f35,f34])).
% 2.66/1.00  
% 2.66/1.00  fof(f54,plain,(
% 2.66/1.00    v1_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f56,plain,(
% 2.66/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f7,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f17,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f7])).
% 2.66/1.00  
% 2.66/1.00  fof(f50,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f17])).
% 2.66/1.00  
% 2.66/1.00  fof(f10,axiom,(
% 2.66/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f20,plain,(
% 2.66/1.00    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.66/1.00    inference(ennf_transformation,[],[f10])).
% 2.66/1.00  
% 2.66/1.00  fof(f21,plain,(
% 2.66/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.66/1.00    inference(flattening,[],[f20])).
% 2.66/1.00  
% 2.66/1.00  fof(f53,plain,(
% 2.66/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f21])).
% 2.66/1.00  
% 2.66/1.00  fof(f55,plain,(
% 2.66/1.00    v1_funct_2(sK3,sK2,sK2)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f58,plain,(
% 2.66/1.00    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f49,plain,(
% 2.66/1.00    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f57,plain,(
% 2.66/1.00    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f9,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f19,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f9])).
% 2.66/1.00  
% 2.66/1.00  fof(f52,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f19])).
% 2.66/1.00  
% 2.66/1.00  fof(f8,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f18,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f8])).
% 2.66/1.00  
% 2.66/1.00  fof(f51,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f18])).
% 2.66/1.00  
% 2.66/1.00  fof(f4,axiom,(
% 2.66/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f26,plain,(
% 2.66/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/1.00    inference(nnf_transformation,[],[f4])).
% 2.66/1.00  
% 2.66/1.00  fof(f42,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f26])).
% 2.66/1.00  
% 2.66/1.00  fof(f46,plain,(
% 2.66/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f3,axiom,(
% 2.66/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f13,plain,(
% 2.66/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/1.00    inference(ennf_transformation,[],[f3])).
% 2.66/1.00  
% 2.66/1.00  fof(f41,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f13])).
% 2.66/1.00  
% 2.66/1.00  fof(f43,plain,(
% 2.66/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f26])).
% 2.66/1.00  
% 2.66/1.00  fof(f47,plain,(
% 2.66/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f2,axiom,(
% 2.66/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f24,plain,(
% 2.66/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/1.00    inference(nnf_transformation,[],[f2])).
% 2.66/1.00  
% 2.66/1.00  fof(f25,plain,(
% 2.66/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/1.00    inference(flattening,[],[f24])).
% 2.66/1.00  
% 2.66/1.00  fof(f38,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f63,plain,(
% 2.66/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.66/1.00    inference(equality_resolution,[],[f38])).
% 2.66/1.00  
% 2.66/1.00  fof(f40,plain,(
% 2.66/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f61,plain,(
% 2.66/1.00    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f45,plain,(
% 2.66/1.00    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f60,plain,(
% 2.66/1.00    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f59,plain,(
% 2.66/1.00    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f1,axiom,(
% 2.66/1.00    v1_xboole_0(k1_xboole_0)),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f37,plain,(
% 2.66/1.00    v1_xboole_0(k1_xboole_0)),
% 2.66/1.00    inference(cnf_transformation,[],[f1])).
% 2.66/1.00  
% 2.66/1.00  fof(f5,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f14,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.66/1.00    inference(ennf_transformation,[],[f5])).
% 2.66/1.00  
% 2.66/1.00  fof(f44,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f14])).
% 2.66/1.00  
% 2.66/1.00  cnf(c_9,plain,
% 2.66/1.00      ( ~ v1_relat_1(X0)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | v2_funct_1(X0)
% 2.66/1.00      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.66/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_24,negated_conjecture,
% 2.66/1.00      ( v1_funct_1(sK3) ),
% 2.66/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_399,plain,
% 2.66/1.00      ( ~ v1_relat_1(X0)
% 2.66/1.00      | v2_funct_1(X0)
% 2.66/1.00      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.66/1.00      | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_400,plain,
% 2.66/1.00      ( ~ v1_relat_1(sK3)
% 2.66/1.00      | v2_funct_1(sK3)
% 2.66/1.00      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2675,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_22,negated_conjecture,
% 2.66/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.66/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_27,plain,
% 2.66/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_401,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_13,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2874,plain,
% 2.66/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.66/1.00      | v1_relat_1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2875,plain,
% 2.66/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2874]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3497,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2675,c_27,c_401,c_2875]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_16,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | ~ r2_hidden(X3,X1)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | ~ v2_funct_1(X0)
% 2.66/1.00      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.66/1.00      | k1_xboole_0 = X2 ),
% 2.66/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_23,negated_conjecture,
% 2.66/1.00      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.66/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_344,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | ~ r2_hidden(X3,X1)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | ~ v2_funct_1(X0)
% 2.66/1.00      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.66/1.00      | sK2 != X2
% 2.66/1.00      | sK2 != X1
% 2.66/1.00      | sK3 != X0
% 2.66/1.00      | k1_xboole_0 = X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_345,plain,
% 2.66/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.66/1.00      | ~ r2_hidden(X0,sK2)
% 2.66/1.00      | ~ v1_funct_1(sK3)
% 2.66/1.00      | ~ v2_funct_1(sK3)
% 2.66/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.66/1.00      | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_344]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_349,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,sK2)
% 2.66/1.00      | ~ v2_funct_1(sK3)
% 2.66/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.66/1.00      | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_345,c_24,c_22]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2094,plain,
% 2.66/1.00      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(splitting,
% 2.66/1.00                [splitting(split),new_symbols(definition,[])],
% 2.66/1.00                [c_349]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2678,plain,
% 2.66/1.00      ( k1_xboole_0 = sK2
% 2.66/1.00      | v2_funct_1(sK3) != iProver_top
% 2.66/1.00      | sP1_iProver_split = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3503,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | sP1_iProver_split = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3497,c_2678]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_20,negated_conjecture,
% 2.66/1.00      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.66/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2684,plain,
% 2.66/1.00      ( r2_hidden(sK4,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2093,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,sK2)
% 2.66/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.66/1.00      | ~ sP1_iProver_split ),
% 2.66/1.00      inference(splitting,
% 2.66/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.66/1.00                [c_349]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2679,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.66/1.00      | r2_hidden(X0,sK2) != iProver_top
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2093]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3247,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.66/1.00      | v2_funct_1(sK3) != iProver_top
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2684,c_2679]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3504,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3497,c_3247]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_25,plain,
% 2.66/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_56,plain,
% 2.66/1.00      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_58,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_56]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_8,plain,
% 2.66/1.00      ( ~ v1_relat_1(X0)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | v2_funct_1(X0)
% 2.66/1.00      | sK1(X0) != sK0(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_59,plain,
% 2.66/1.00      ( sK1(X0) != sK0(X0)
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_61,plain,
% 2.66/1.00      ( sK1(sK3) != sK0(sK3)
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_21,negated_conjecture,
% 2.66/1.00      ( ~ r2_hidden(X0,sK2)
% 2.66/1.00      | ~ r2_hidden(X1,sK2)
% 2.66/1.00      | v2_funct_1(sK3)
% 2.66/1.00      | X1 = X0
% 2.66/1.00      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2963,plain,
% 2.66/1.00      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.66/1.00      | ~ r2_hidden(sK0(sK3),sK2)
% 2.66/1.00      | v2_funct_1(sK3)
% 2.66/1.00      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | sK1(sK3) = sK0(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2964,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.66/1.00      | sK1(sK3) = sK0(sK3)
% 2.66/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.66/1.00      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2682,plain,
% 2.66/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_15,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2688,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.66/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3542,plain,
% 2.66/1.00      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2682,c_2688]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_14,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.66/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2689,plain,
% 2.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.66/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3735,plain,
% 2.66/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.66/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3542,c_2689]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4001,plain,
% 2.66/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3735,c_27]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_6,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2691,plain,
% 2.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.66/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4006,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4001,c_2691]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_11,plain,
% 2.66/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | v2_funct_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_373,plain,
% 2.66/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | v2_funct_1(X0)
% 2.66/1.00      | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_374,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.66/1.00      | ~ v1_relat_1(sK3)
% 2.66/1.00      | v2_funct_1(sK3) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_373]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2677,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_375,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3879,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2677,c_27,c_375,c_2875]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.66/1.00      | ~ r2_hidden(X2,X0)
% 2.66/1.00      | r2_hidden(X2,X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5,plain,
% 2.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_190,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.66/1.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_191,plain,
% 2.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_190]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_239,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.66/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_191]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2681,plain,
% 2.66/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.66/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.66/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4208,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3879,c_2681]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4556,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4006,c_4208]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_10,plain,
% 2.66/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | v2_funct_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_386,plain,
% 2.66/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | v2_funct_1(X0)
% 2.66/1.00      | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_387,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.66/1.00      | ~ v1_relat_1(sK3)
% 2.66/1.00      | v2_funct_1(sK3) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2676,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_388,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3427,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2676,c_27,c_388,c_2875]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4209,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),X0) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3427,c_2681]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4567,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4006,c_4209]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4691,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3504,c_25,c_27,c_58,c_61,c_2875,c_2964,c_3247,c_4556,c_4567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4697,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3503,c_4691]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_73,plain,
% 2.66/1.00      ( r1_tarski(sK3,sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.66/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_77,plain,
% 2.66/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_412,plain,
% 2.66/1.00      ( ~ v1_relat_1(X0) | v2_funct_1(X0) | sK1(X0) != sK0(X0) | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_413,plain,
% 2.66/1.00      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_17,negated_conjecture,
% 2.66/1.00      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.66/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_653,plain,
% 2.66/1.00      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.66/1.00      inference(resolution,[status(thm)],[c_413,c_17]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_744,plain,
% 2.66/1.00      ( ~ v1_relat_1(sK3)
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sK5 != sK4 ),
% 2.66/1.00      inference(resolution,[status(thm)],[c_400,c_17]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_835,plain,
% 2.66/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.66/1.00      inference(resolution,[status(thm)],[c_387,c_17]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_926,plain,
% 2.66/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.66/1.00      inference(resolution,[status(thm)],[c_374,c_17]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2104,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2116,plain,
% 2.66/1.00      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2104]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_12,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.66/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.66/1.00      | ~ v1_relat_1(X1)
% 2.66/1.00      | ~ v1_funct_1(X1)
% 2.66/1.00      | ~ v2_funct_1(X1)
% 2.66/1.00      | X0 = X2
% 2.66/1.00      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.66/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_425,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.66/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.66/1.00      | ~ v1_relat_1(X1)
% 2.66/1.00      | ~ v2_funct_1(X1)
% 2.66/1.00      | X2 = X0
% 2.66/1.00      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.66/1.00      | sK3 != X1 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_426,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.66/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.66/1.00      | ~ v1_relat_1(sK3)
% 2.66/1.00      | ~ v2_funct_1(sK3)
% 2.66/1.00      | X0 = X1
% 2.66/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2092,plain,
% 2.66/1.00      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 2.66/1.00      inference(splitting,
% 2.66/1.00                [splitting(split),new_symbols(definition,[])],
% 2.66/1.00                [c_426]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2097,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2966,plain,
% 2.66/1.00      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2097]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3079,plain,
% 2.66/1.00      ( sK1(sK3) != sK1(sK3) | sK1(sK3) = sK0(sK3) | sK0(sK3) != sK1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2966]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2091,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.66/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.66/1.00      | X0 = X1
% 2.66/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.66/1.00      | ~ sP0_iProver_split ),
% 2.66/1.00      inference(splitting,
% 2.66/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.66/1.00                [c_426]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4455,plain,
% 2.66/1.00      ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
% 2.66/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.66/1.00      | ~ sP0_iProver_split
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 2.66/1.00      | sK0(sK3) = sK1(X0) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2091]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4457,plain,
% 2.66/1.00      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.66/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.66/1.00      | ~ sP0_iProver_split
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sK0(sK3) = sK1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_4455]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_18,negated_conjecture,
% 2.66/1.00      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.66/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2686,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3507,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3497,c_2686]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2683,plain,
% 2.66/1.00      ( X0 = X1
% 2.66/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.66/1.00      | r2_hidden(X1,sK2) != iProver_top
% 2.66/1.00      | r2_hidden(X0,sK2) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3742,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.66/1.00      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.66/1.00      | sK1(sK3) = X0
% 2.66/1.00      | r2_hidden(X0,sK2) != iProver_top
% 2.66/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3507,c_2683]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3893,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.66/1.00      | sK1(sK3) = sK0(sK3)
% 2.66/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.66/1.00      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.66/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(equality_resolution,[status(thm)],[c_3742]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4775,plain,
% 2.66/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3893,c_25,c_27,c_58,c_61,c_2875,c_2964,c_4556,c_4567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4777,plain,
% 2.66/1.00      ( v2_funct_1(sK3) ),
% 2.66/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4775]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4780,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4775,c_2678]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4784,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4775,c_2686]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_19,negated_conjecture,
% 2.66/1.00      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.66/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2685,plain,
% 2.66/1.00      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3246,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.66/1.00      | v2_funct_1(sK3) != iProver_top
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2685,c_2679]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3505,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3497,c_3246]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4699,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3505,c_25,c_27,c_58,c_61,c_2875,c_2964,c_3246,c_4556,c_4567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4796,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_4784,c_4699]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5147,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.66/1.00      | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4780,c_4796]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5148,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.66/1.00      | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_4780,c_4691]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5644,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_5147,c_5148]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5646,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_4697,c_22,c_73,c_77,c_653,c_744,c_835,c_926,c_2116,c_2092,
% 2.66/1.00                 c_2874,c_3079,c_4457,c_4777,c_5644]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5661,plain,
% 2.66/1.00      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 2.66/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_5646,c_2685]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5837,plain,
% 2.66/1.00      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_5661,c_25,c_27,c_58,c_61,c_2875,c_2964,c_4556,c_4567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5658,plain,
% 2.66/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.66/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.66/1.00      | sP1_iProver_split != iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_5646,c_2679]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_0,plain,
% 2.66/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_7,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.66/1.00      | ~ r2_hidden(X2,X0)
% 2.66/1.00      | ~ v1_xboole_0(X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_242,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.66/1.00      inference(bin_hyper_res,[status(thm)],[c_7,c_191]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_329,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_242]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_330,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_329]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2913,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_xboole_0) | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_330]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2915,plain,
% 2.66/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.66/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2913]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2914,plain,
% 2.66/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2919,plain,
% 2.66/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2914]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_6315,plain,
% 2.66/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_5658,c_2915,c_2919]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_6322,plain,
% 2.66/1.00      ( $false ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_5837,c_6315]) ).
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  ------                               Statistics
% 2.66/1.00  
% 2.66/1.00  ------ General
% 2.66/1.00  
% 2.66/1.00  abstr_ref_over_cycles:                  0
% 2.66/1.00  abstr_ref_under_cycles:                 0
% 2.66/1.00  gc_basic_clause_elim:                   0
% 2.66/1.00  forced_gc_time:                         0
% 2.66/1.00  parsing_time:                           0.014
% 2.66/1.00  unif_index_cands_time:                  0.
% 2.66/1.00  unif_index_add_time:                    0.
% 2.66/1.00  orderings_time:                         0.
% 2.66/1.00  out_proof_time:                         0.011
% 2.66/1.00  total_time:                             0.205
% 2.66/1.00  num_of_symbols:                         54
% 2.66/1.00  num_of_terms:                           3486
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing
% 2.66/1.00  
% 2.66/1.00  num_of_splits:                          2
% 2.66/1.00  num_of_split_atoms:                     2
% 2.66/1.00  num_of_reused_defs:                     0
% 2.66/1.00  num_eq_ax_congr_red:                    18
% 2.66/1.00  num_of_sem_filtered_clauses:            1
% 2.66/1.00  num_of_subtypes:                        0
% 2.66/1.00  monotx_restored_types:                  0
% 2.66/1.00  sat_num_of_epr_types:                   0
% 2.66/1.00  sat_num_of_non_cyclic_types:            0
% 2.66/1.00  sat_guarded_non_collapsed_types:        0
% 2.66/1.00  num_pure_diseq_elim:                    0
% 2.66/1.00  simp_replaced_by:                       0
% 2.66/1.00  res_preprocessed:                       120
% 2.66/1.00  prep_upred:                             0
% 2.66/1.00  prep_unflattend:                        19
% 2.66/1.00  smt_new_axioms:                         0
% 2.66/1.00  pred_elim_cands:                        5
% 2.66/1.00  pred_elim:                              3
% 2.66/1.00  pred_elim_cl:                           3
% 2.66/1.00  pred_elim_cycles:                       7
% 2.66/1.00  merged_defs:                            8
% 2.66/1.00  merged_defs_ncl:                        0
% 2.66/1.00  bin_hyper_res:                          10
% 2.66/1.00  prep_cycles:                            4
% 2.66/1.00  pred_elim_time:                         0.03
% 2.66/1.00  splitting_time:                         0.
% 2.66/1.00  sem_filter_time:                        0.
% 2.66/1.00  monotx_time:                            0.
% 2.66/1.00  subtype_inf_time:                       0.
% 2.66/1.00  
% 2.66/1.00  ------ Problem properties
% 2.66/1.00  
% 2.66/1.00  clauses:                                23
% 2.66/1.00  conjectures:                            6
% 2.66/1.00  epr:                                    9
% 2.66/1.00  horn:                                   18
% 2.66/1.00  ground:                                 11
% 2.66/1.00  unary:                                  2
% 2.66/1.00  binary:                                 10
% 2.66/1.00  lits:                                   59
% 2.66/1.00  lits_eq:                                12
% 2.66/1.00  fd_pure:                                0
% 2.66/1.00  fd_pseudo:                              0
% 2.66/1.00  fd_cond:                                0
% 2.66/1.00  fd_pseudo_cond:                         3
% 2.66/1.00  ac_symbols:                             0
% 2.66/1.00  
% 2.66/1.00  ------ Propositional Solver
% 2.66/1.00  
% 2.66/1.00  prop_solver_calls:                      30
% 2.66/1.00  prop_fast_solver_calls:                 1168
% 2.66/1.00  smt_solver_calls:                       0
% 2.66/1.00  smt_fast_solver_calls:                  0
% 2.66/1.00  prop_num_of_clauses:                    1696
% 2.66/1.00  prop_preprocess_simplified:             5652
% 2.66/1.00  prop_fo_subsumed:                       32
% 2.66/1.00  prop_solver_time:                       0.
% 2.66/1.00  smt_solver_time:                        0.
% 2.66/1.00  smt_fast_solver_time:                   0.
% 2.66/1.00  prop_fast_solver_time:                  0.
% 2.66/1.00  prop_unsat_core_time:                   0.
% 2.66/1.00  
% 2.66/1.00  ------ QBF
% 2.66/1.00  
% 2.66/1.00  qbf_q_res:                              0
% 2.66/1.00  qbf_num_tautologies:                    0
% 2.66/1.00  qbf_prep_cycles:                        0
% 2.66/1.00  
% 2.66/1.00  ------ BMC1
% 2.66/1.00  
% 2.66/1.00  bmc1_current_bound:                     -1
% 2.66/1.00  bmc1_last_solved_bound:                 -1
% 2.66/1.00  bmc1_unsat_core_size:                   -1
% 2.66/1.00  bmc1_unsat_core_parents_size:           -1
% 2.66/1.00  bmc1_merge_next_fun:                    0
% 2.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation
% 2.66/1.00  
% 2.66/1.00  inst_num_of_clauses:                    507
% 2.66/1.00  inst_num_in_passive:                    144
% 2.66/1.00  inst_num_in_active:                     339
% 2.66/1.00  inst_num_in_unprocessed:                24
% 2.66/1.00  inst_num_of_loops:                      370
% 2.66/1.00  inst_num_of_learning_restarts:          0
% 2.66/1.00  inst_num_moves_active_passive:          26
% 2.66/1.00  inst_lit_activity:                      0
% 2.66/1.00  inst_lit_activity_moves:                0
% 2.66/1.00  inst_num_tautologies:                   0
% 2.66/1.00  inst_num_prop_implied:                  0
% 2.66/1.00  inst_num_existing_simplified:           0
% 2.66/1.00  inst_num_eq_res_simplified:             0
% 2.66/1.00  inst_num_child_elim:                    0
% 2.66/1.00  inst_num_of_dismatching_blockings:      167
% 2.66/1.00  inst_num_of_non_proper_insts:           749
% 2.66/1.00  inst_num_of_duplicates:                 0
% 2.66/1.00  inst_inst_num_from_inst_to_res:         0
% 2.66/1.00  inst_dismatching_checking_time:         0.
% 2.66/1.00  
% 2.66/1.00  ------ Resolution
% 2.66/1.00  
% 2.66/1.00  res_num_of_clauses:                     0
% 2.66/1.00  res_num_in_passive:                     0
% 2.66/1.00  res_num_in_active:                      0
% 2.66/1.00  res_num_of_loops:                       124
% 2.66/1.00  res_forward_subset_subsumed:            81
% 2.66/1.00  res_backward_subset_subsumed:           2
% 2.66/1.00  res_forward_subsumed:                   0
% 2.66/1.00  res_backward_subsumed:                  0
% 2.66/1.00  res_forward_subsumption_resolution:     0
% 2.66/1.00  res_backward_subsumption_resolution:    0
% 2.66/1.00  res_clause_to_clause_subsumption:       211
% 2.66/1.00  res_orphan_elimination:                 0
% 2.66/1.00  res_tautology_del:                      120
% 2.66/1.00  res_num_eq_res_simplified:              0
% 2.66/1.00  res_num_sel_changes:                    0
% 2.66/1.00  res_moves_from_active_to_pass:          0
% 2.66/1.00  
% 2.66/1.00  ------ Superposition
% 2.66/1.00  
% 2.66/1.00  sup_time_total:                         0.
% 2.66/1.00  sup_time_generating:                    0.
% 2.66/1.00  sup_time_sim_full:                      0.
% 2.66/1.00  sup_time_sim_immed:                     0.
% 2.66/1.00  
% 2.66/1.00  sup_num_of_clauses:                     77
% 2.66/1.00  sup_num_in_active:                      54
% 2.66/1.00  sup_num_in_passive:                     23
% 2.66/1.00  sup_num_of_loops:                       73
% 2.66/1.00  sup_fw_superposition:                   46
% 2.66/1.00  sup_bw_superposition:                   57
% 2.66/1.00  sup_immediate_simplified:               17
% 2.66/1.00  sup_given_eliminated:                   0
% 2.66/1.00  comparisons_done:                       0
% 2.66/1.00  comparisons_avoided:                    12
% 2.66/1.00  
% 2.66/1.00  ------ Simplifications
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  sim_fw_subset_subsumed:                 8
% 2.66/1.00  sim_bw_subset_subsumed:                 4
% 2.66/1.00  sim_fw_subsumed:                        1
% 2.66/1.00  sim_bw_subsumed:                        1
% 2.66/1.00  sim_fw_subsumption_res:                 0
% 2.66/1.00  sim_bw_subsumption_res:                 0
% 2.66/1.00  sim_tautology_del:                      1
% 2.66/1.00  sim_eq_tautology_del:                   9
% 2.66/1.00  sim_eq_res_simp:                        0
% 2.66/1.00  sim_fw_demodulated:                     3
% 2.66/1.00  sim_bw_demodulated:                     22
% 2.66/1.00  sim_light_normalised:                   3
% 2.66/1.00  sim_joinable_taut:                      0
% 2.66/1.00  sim_joinable_simp:                      0
% 2.66/1.00  sim_ac_normalised:                      0
% 2.66/1.00  sim_smt_subsumption:                    0
% 2.66/1.00  
%------------------------------------------------------------------------------
