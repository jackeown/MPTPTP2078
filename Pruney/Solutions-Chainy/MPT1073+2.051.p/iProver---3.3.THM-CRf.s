%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:10 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  155 (4037 expanded)
%              Number of clauses        :   94 (1256 expanded)
%              Number of leaves         :   19 ( 865 expanded)
%              Depth                    :   26
%              Number of atoms          :  521 (19399 expanded)
%              Number of equality atoms :  248 (5520 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK3
          | ~ m1_subset_1(X4,sK4) )
      & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK3
        | ~ m1_subset_1(X4,sK4) )
    & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f36])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK3
      | ~ m1_subset_1(X4,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_715,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_718,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1183,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_718])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1184,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1183])).

cnf(c_1616,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_25,c_1184])).

cnf(c_1617,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1616])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_725,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1343,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_715,c_725])).

cnf(c_1618,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1617,c_1343])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_724,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1339,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_715,c_724])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_716,plain,
    ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1487,plain,
    ( r2_hidden(sK3,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1339,c_716])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_730,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2272,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK3)) = sK3
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_730])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1057,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_3,c_24])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1062,plain,
    ( v1_relat_1(sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1057,c_4])).

cnf(c_1488,plain,
    ( r2_hidden(sK3,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1487])).

cnf(c_1659,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2275,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_26,c_1062,c_1488,c_1659])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_728,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2728,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK3),sK3),sK6) = iProver_top
    | r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_728])).

cnf(c_27,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1063,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1660,plain,
    ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6))
    | ~ r2_hidden(sK3,k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1661,plain,
    ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_3217,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK3),sK3),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_27,c_1063,c_1487,c_1661])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_726,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3224,plain,
    ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_726])).

cnf(c_3547,plain,
    ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_27,c_1063,c_1487,c_1661])).

cnf(c_3552,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_3547])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_737,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3570,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK2(sK6,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_737])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK6,X0) != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(sK2(sK6,sK3),sK4)
    | k1_funct_1(sK6,sK2(sK6,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2259,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK3)) != sK3
    | m1_subset_1(sK2(sK6,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_3644,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3570,c_26,c_1062,c_1488,c_1659,c_2259])).

cnf(c_3650,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3644,c_715])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_722,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3818,plain,
    ( sK4 = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3650,c_722])).

cnf(c_28,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_252,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_279,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_1172,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_265,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1086,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X2 != sK5
    | X1 != sK4
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1318,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X1 != sK5
    | X0 != sK4
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1697,plain,
    ( v1_funct_2(sK6,sK4,X0)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK5
    | sK4 != sK4
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_1699,plain,
    ( X0 != sK5
    | sK4 != sK4
    | sK6 != sK6
    | v1_funct_2(sK6,sK4,X0) = iProver_top
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_1701,plain,
    ( sK4 != sK4
    | sK6 != sK6
    | k1_xboole_0 != sK5
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_1698,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_253,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2226,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_2227,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_739,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3222,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_739])).

cnf(c_3236,plain,
    ( ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3222])).

cnf(c_255,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3524,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_3526,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3524])).

cnf(c_4120,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_26,c_28,c_1,c_279,c_1062,c_1172,c_1488,c_1659,c_1701,c_1698,c_2227,c_2259,c_3236,c_3526,c_3570])).

cnf(c_3648,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_3644,c_1343])).

cnf(c_4124,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_4120,c_3648])).

cnf(c_4125,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4120,c_3650])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_719,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4304,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4125,c_719])).

cnf(c_1321,plain,
    ( X0 != sK5
    | X1 != sK4
    | sK6 != sK6
    | v1_funct_2(sK6,X1,X0) = iProver_top
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_1323,plain,
    ( sK6 != sK6
    | k1_xboole_0 != sK5
    | k1_xboole_0 != sK4
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1703,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1704,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_4624,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4304,c_26,c_28,c_1,c_279,c_1062,c_1172,c_1323,c_1488,c_1659,c_1701,c_1698,c_1704,c_2227,c_2259,c_3236,c_3526,c_3570,c_3818])).

cnf(c_4706,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4124,c_4624])).

cnf(c_3529,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK6))
    | k1_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_3531,plain,
    ( v1_xboole_0(k1_relat_1(sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3529])).

cnf(c_2321,plain,
    ( ~ r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6))
    | ~ v1_xboole_0(k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4706,c_3531,c_2321,c_1660,c_1488,c_1062,c_1,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:23:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.37/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.05  
% 0.37/1.05  ------  iProver source info
% 0.37/1.05  
% 0.37/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.05  git: non_committed_changes: false
% 0.37/1.05  git: last_make_outside_of_git: false
% 0.37/1.05  
% 0.37/1.05  ------ 
% 0.37/1.05  ------ Parsing...
% 0.37/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.05  ------ Proving...
% 0.37/1.05  ------ Problem Properties 
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  clauses                                 27
% 0.37/1.05  conjectures                             5
% 0.37/1.05  EPR                                     5
% 0.37/1.05  Horn                                    21
% 0.37/1.05  unary                                   6
% 0.37/1.05  binary                                  5
% 0.37/1.05  lits                                    80
% 0.37/1.05  lits eq                                 19
% 0.37/1.05  fd_pure                                 0
% 0.37/1.05  fd_pseudo                               0
% 0.37/1.05  fd_cond                                 3
% 0.37/1.05  fd_pseudo_cond                          4
% 0.37/1.05  AC symbols                              0
% 0.37/1.05  
% 0.37/1.05  ------ Input Options Time Limit: Unbounded
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  ------ 
% 0.37/1.05  Current options:
% 0.37/1.05  ------ 
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  ------ Proving...
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  % SZS status Theorem for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  fof(f11,conjecture,(
% 0.37/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f12,negated_conjecture,(
% 0.37/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.37/1.05    inference(negated_conjecture,[],[f11])).
% 0.37/1.05  
% 0.37/1.05  fof(f25,plain,(
% 0.37/1.05    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.37/1.05    inference(ennf_transformation,[],[f12])).
% 0.37/1.05  
% 0.37/1.05  fof(f26,plain,(
% 0.37/1.05    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.37/1.05    inference(flattening,[],[f25])).
% 0.37/1.05  
% 0.37/1.05  fof(f36,plain,(
% 0.37/1.05    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 0.37/1.05    introduced(choice_axiom,[])).
% 0.37/1.05  
% 0.37/1.05  fof(f37,plain,(
% 0.37/1.05    ! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 0.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f36])).
% 0.37/1.05  
% 0.37/1.05  fof(f62,plain,(
% 0.37/1.05    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.37/1.05    inference(cnf_transformation,[],[f37])).
% 0.37/1.05  
% 0.37/1.05  fof(f10,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f23,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.05    inference(ennf_transformation,[],[f10])).
% 0.37/1.05  
% 0.37/1.05  fof(f24,plain,(
% 0.37/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.05    inference(flattening,[],[f23])).
% 0.37/1.05  
% 0.37/1.05  fof(f35,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.05    inference(nnf_transformation,[],[f24])).
% 0.37/1.05  
% 0.37/1.05  fof(f54,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f35])).
% 0.37/1.05  
% 0.37/1.05  fof(f61,plain,(
% 0.37/1.05    v1_funct_2(sK6,sK4,sK5)),
% 0.37/1.05    inference(cnf_transformation,[],[f37])).
% 0.37/1.05  
% 0.37/1.05  fof(f8,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f21,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.05    inference(ennf_transformation,[],[f8])).
% 0.37/1.05  
% 0.37/1.05  fof(f52,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f21])).
% 0.37/1.05  
% 0.37/1.05  fof(f9,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f22,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.05    inference(ennf_transformation,[],[f9])).
% 0.37/1.05  
% 0.37/1.05  fof(f53,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f22])).
% 0.37/1.05  
% 0.37/1.05  fof(f63,plain,(
% 0.37/1.05    r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))),
% 0.37/1.05    inference(cnf_transformation,[],[f37])).
% 0.37/1.05  
% 0.37/1.05  fof(f6,axiom,(
% 0.37/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f17,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.05    inference(ennf_transformation,[],[f6])).
% 0.37/1.05  
% 0.37/1.05  fof(f18,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.05    inference(flattening,[],[f17])).
% 0.37/1.05  
% 0.37/1.05  fof(f27,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.05    inference(nnf_transformation,[],[f18])).
% 0.37/1.05  
% 0.37/1.05  fof(f28,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.05    inference(rectify,[],[f27])).
% 0.37/1.05  
% 0.37/1.05  fof(f31,plain,(
% 0.37/1.05    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 0.37/1.05    introduced(choice_axiom,[])).
% 0.37/1.05  
% 0.37/1.05  fof(f30,plain,(
% 0.37/1.05    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 0.37/1.05    introduced(choice_axiom,[])).
% 0.37/1.05  
% 0.37/1.05  fof(f29,plain,(
% 0.37/1.05    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 0.37/1.05    introduced(choice_axiom,[])).
% 0.37/1.05  
% 0.37/1.05  fof(f32,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).
% 0.37/1.05  
% 0.37/1.05  fof(f44,plain,(
% 0.37/1.05    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f32])).
% 0.37/1.05  
% 0.37/1.05  fof(f67,plain,(
% 0.37/1.05    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.05    inference(equality_resolution,[],[f44])).
% 0.37/1.05  
% 0.37/1.05  fof(f60,plain,(
% 0.37/1.05    v1_funct_1(sK6)),
% 0.37/1.05    inference(cnf_transformation,[],[f37])).
% 0.37/1.05  
% 0.37/1.05  fof(f4,axiom,(
% 0.37/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f16,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.37/1.05    inference(ennf_transformation,[],[f4])).
% 0.37/1.05  
% 0.37/1.05  fof(f41,plain,(
% 0.37/1.05    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f16])).
% 0.37/1.05  
% 0.37/1.05  fof(f5,axiom,(
% 0.37/1.05    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f42,plain,(
% 0.37/1.05    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f5])).
% 0.37/1.05  
% 0.37/1.05  fof(f7,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f19,plain,(
% 0.37/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.37/1.05    inference(ennf_transformation,[],[f7])).
% 0.37/1.05  
% 0.37/1.05  fof(f20,plain,(
% 0.37/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/1.05    inference(flattening,[],[f19])).
% 0.37/1.05  
% 0.37/1.05  fof(f33,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/1.05    inference(nnf_transformation,[],[f20])).
% 0.37/1.05  
% 0.37/1.05  fof(f34,plain,(
% 0.37/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/1.05    inference(flattening,[],[f33])).
% 0.37/1.05  
% 0.37/1.05  fof(f51,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f34])).
% 0.37/1.05  
% 0.37/1.05  fof(f69,plain,(
% 0.37/1.05    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.37/1.05    inference(equality_resolution,[],[f51])).
% 0.37/1.05  
% 0.37/1.05  fof(f43,plain,(
% 0.37/1.05    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f32])).
% 0.37/1.05  
% 0.37/1.05  fof(f68,plain,(
% 0.37/1.05    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.05    inference(equality_resolution,[],[f43])).
% 0.37/1.05  
% 0.37/1.05  fof(f49,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f34])).
% 0.37/1.05  
% 0.37/1.05  fof(f3,axiom,(
% 0.37/1.05    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f15,plain,(
% 0.37/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.37/1.05    inference(ennf_transformation,[],[f3])).
% 0.37/1.05  
% 0.37/1.05  fof(f40,plain,(
% 0.37/1.05    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f15])).
% 0.37/1.05  
% 0.37/1.05  fof(f64,plain,(
% 0.37/1.05    ( ! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f37])).
% 0.37/1.05  
% 0.37/1.05  fof(f58,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f35])).
% 0.37/1.05  
% 0.37/1.05  fof(f72,plain,(
% 0.37/1.05    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.37/1.05    inference(equality_resolution,[],[f58])).
% 0.37/1.05  
% 0.37/1.05  fof(f2,axiom,(
% 0.37/1.05    v1_xboole_0(k1_xboole_0)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f39,plain,(
% 0.37/1.05    v1_xboole_0(k1_xboole_0)),
% 0.37/1.05    inference(cnf_transformation,[],[f2])).
% 0.37/1.05  
% 0.37/1.05  fof(f1,axiom,(
% 0.37/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f13,plain,(
% 0.37/1.05    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.37/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 0.37/1.05  
% 0.37/1.05  fof(f14,plain,(
% 0.37/1.05    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.37/1.05    inference(ennf_transformation,[],[f13])).
% 0.37/1.05  
% 0.37/1.05  fof(f38,plain,(
% 0.37/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f14])).
% 0.37/1.05  
% 0.37/1.05  fof(f55,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f35])).
% 0.37/1.05  
% 0.37/1.05  fof(f74,plain,(
% 0.37/1.05    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.37/1.05    inference(equality_resolution,[],[f55])).
% 0.37/1.05  
% 0.37/1.05  cnf(c_24,negated_conjecture,
% 0.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 0.37/1.05      inference(cnf_transformation,[],[f62]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_715,plain,
% 0.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_21,plain,
% 0.37/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.05      | k1_relset_1(X1,X2,X0) = X1
% 0.37/1.05      | k1_xboole_0 = X2 ),
% 0.37/1.05      inference(cnf_transformation,[],[f54]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_718,plain,
% 0.37/1.05      ( k1_relset_1(X0,X1,X2) = X0
% 0.37/1.05      | k1_xboole_0 = X1
% 0.37/1.05      | v1_funct_2(X2,X0,X1) != iProver_top
% 0.37/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1183,plain,
% 0.37/1.05      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 0.37/1.05      | sK5 = k1_xboole_0
% 0.37/1.05      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_715,c_718]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_25,negated_conjecture,
% 0.37/1.05      ( v1_funct_2(sK6,sK4,sK5) ),
% 0.37/1.05      inference(cnf_transformation,[],[f61]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1184,plain,
% 0.37/1.05      ( ~ v1_funct_2(sK6,sK4,sK5)
% 0.37/1.05      | k1_relset_1(sK4,sK5,sK6) = sK4
% 0.37/1.05      | sK5 = k1_xboole_0 ),
% 0.37/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_1183]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1616,plain,
% 0.37/1.05      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_1183,c_25,c_1184]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1617,plain,
% 0.37/1.05      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 0.37/1.05      inference(renaming,[status(thm)],[c_1616]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_14,plain,
% 0.37/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.37/1.05      inference(cnf_transformation,[],[f52]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_725,plain,
% 0.37/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.37/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1343,plain,
% 0.37/1.05      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_715,c_725]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1618,plain,
% 0.37/1.05      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_1617,c_1343]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_15,plain,
% 0.37/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.37/1.05      inference(cnf_transformation,[],[f53]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_724,plain,
% 0.37/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.37/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1339,plain,
% 0.37/1.05      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_715,c_724]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_23,negated_conjecture,
% 0.37/1.05      ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
% 0.37/1.05      inference(cnf_transformation,[],[f63]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_716,plain,
% 0.37/1.05      ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1487,plain,
% 0.37/1.05      ( r2_hidden(sK3,k2_relat_1(sK6)) = iProver_top ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_1339,c_716]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_9,plain,
% 0.37/1.05      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 0.37/1.05      | ~ v1_funct_1(X1)
% 0.37/1.05      | ~ v1_relat_1(X1)
% 0.37/1.05      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 0.37/1.05      inference(cnf_transformation,[],[f67]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_730,plain,
% 0.37/1.05      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 0.37/1.05      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 0.37/1.05      | v1_funct_1(X0) != iProver_top
% 0.37/1.05      | v1_relat_1(X0) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2272,plain,
% 0.37/1.05      ( k1_funct_1(sK6,sK2(sK6,sK3)) = sK3
% 0.37/1.05      | v1_funct_1(sK6) != iProver_top
% 0.37/1.05      | v1_relat_1(sK6) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_1487,c_730]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_26,negated_conjecture,
% 0.37/1.05      ( v1_funct_1(sK6) ),
% 0.37/1.05      inference(cnf_transformation,[],[f60]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3,plain,
% 0.37/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.37/1.05      | ~ v1_relat_1(X1)
% 0.37/1.05      | v1_relat_1(X0) ),
% 0.37/1.05      inference(cnf_transformation,[],[f41]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1057,plain,
% 0.37/1.05      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) | v1_relat_1(sK6) ),
% 0.37/1.05      inference(resolution,[status(thm)],[c_3,c_24]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4,plain,
% 0.37/1.05      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.37/1.05      inference(cnf_transformation,[],[f42]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1062,plain,
% 0.37/1.05      ( v1_relat_1(sK6) ),
% 0.37/1.05      inference(forward_subsumption_resolution,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_1057,c_4]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1488,plain,
% 0.37/1.05      ( r2_hidden(sK3,k2_relat_1(sK6)) ),
% 0.37/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_1487]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1659,plain,
% 0.37/1.05      ( ~ r2_hidden(sK3,k2_relat_1(sK6))
% 0.37/1.05      | ~ v1_funct_1(sK6)
% 0.37/1.05      | ~ v1_relat_1(sK6)
% 0.37/1.05      | k1_funct_1(sK6,sK2(sK6,sK3)) = sK3 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_9]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2275,plain,
% 0.37/1.05      ( k1_funct_1(sK6,sK2(sK6,sK3)) = sK3 ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_2272,c_26,c_1062,c_1488,c_1659]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_11,plain,
% 0.37/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 0.37/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 0.37/1.05      | ~ v1_funct_1(X1)
% 0.37/1.05      | ~ v1_relat_1(X1) ),
% 0.37/1.05      inference(cnf_transformation,[],[f69]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_728,plain,
% 0.37/1.05      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 0.37/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 0.37/1.05      | v1_funct_1(X1) != iProver_top
% 0.37/1.05      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2728,plain,
% 0.37/1.05      ( r2_hidden(k4_tarski(sK2(sK6,sK3),sK3),sK6) = iProver_top
% 0.37/1.05      | r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) != iProver_top
% 0.37/1.05      | v1_funct_1(sK6) != iProver_top
% 0.37/1.05      | v1_relat_1(sK6) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_2275,c_728]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_27,plain,
% 0.37/1.05      ( v1_funct_1(sK6) = iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1063,plain,
% 0.37/1.05      ( v1_relat_1(sK6) = iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_10,plain,
% 0.37/1.05      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 0.37/1.05      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 0.37/1.05      | ~ v1_funct_1(X1)
% 0.37/1.05      | ~ v1_relat_1(X1) ),
% 0.37/1.05      inference(cnf_transformation,[],[f68]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1660,plain,
% 0.37/1.05      ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6))
% 0.37/1.05      | ~ r2_hidden(sK3,k2_relat_1(sK6))
% 0.37/1.05      | ~ v1_funct_1(sK6)
% 0.37/1.05      | ~ v1_relat_1(sK6) ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1661,plain,
% 0.37/1.05      ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top
% 0.37/1.05      | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top
% 0.37/1.05      | v1_funct_1(sK6) != iProver_top
% 0.37/1.05      | v1_relat_1(sK6) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3217,plain,
% 0.37/1.05      ( r2_hidden(k4_tarski(sK2(sK6,sK3),sK3),sK6) = iProver_top ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_2728,c_27,c_1063,c_1487,c_1661]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_13,plain,
% 0.37/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 0.37/1.05      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 0.37/1.05      | ~ v1_funct_1(X1)
% 0.37/1.05      | ~ v1_relat_1(X1) ),
% 0.37/1.05      inference(cnf_transformation,[],[f49]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_726,plain,
% 0.37/1.05      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 0.37/1.05      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 0.37/1.05      | v1_funct_1(X1) != iProver_top
% 0.37/1.05      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3224,plain,
% 0.37/1.05      ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top
% 0.37/1.05      | v1_funct_1(sK6) != iProver_top
% 0.37/1.05      | v1_relat_1(sK6) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_3217,c_726]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3547,plain,
% 0.37/1.05      ( r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6)) = iProver_top ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_3224,c_27,c_1063,c_1487,c_1661]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3552,plain,
% 0.37/1.05      ( sK5 = k1_xboole_0 | r2_hidden(sK2(sK6,sK3),sK4) = iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_1618,c_3547]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2,plain,
% 0.37/1.05      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 0.37/1.05      inference(cnf_transformation,[],[f40]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_737,plain,
% 0.37/1.05      ( m1_subset_1(X0,X1) = iProver_top
% 0.37/1.05      | r2_hidden(X0,X1) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3570,plain,
% 0.37/1.05      ( sK5 = k1_xboole_0 | m1_subset_1(sK2(sK6,sK3),sK4) = iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_3552,c_737]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_22,negated_conjecture,
% 0.37/1.05      ( ~ m1_subset_1(X0,sK4) | k1_funct_1(sK6,X0) != sK3 ),
% 0.37/1.05      inference(cnf_transformation,[],[f64]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2258,plain,
% 0.37/1.05      ( ~ m1_subset_1(sK2(sK6,sK3),sK4)
% 0.37/1.05      | k1_funct_1(sK6,sK2(sK6,sK3)) != sK3 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_22]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2259,plain,
% 0.37/1.05      ( k1_funct_1(sK6,sK2(sK6,sK3)) != sK3
% 0.37/1.05      | m1_subset_1(sK2(sK6,sK3),sK4) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3644,plain,
% 0.37/1.05      ( sK5 = k1_xboole_0 ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_3570,c_26,c_1062,c_1488,c_1659,c_2259]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3650,plain,
% 0.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_3644,c_715]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_17,plain,
% 0.37/1.05      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 0.37/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 0.37/1.05      | k1_xboole_0 = X1
% 0.37/1.05      | k1_xboole_0 = X0 ),
% 0.37/1.05      inference(cnf_transformation,[],[f72]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_722,plain,
% 0.37/1.05      ( k1_xboole_0 = X0
% 0.37/1.05      | k1_xboole_0 = X1
% 0.37/1.05      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 0.37/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3818,plain,
% 0.37/1.05      ( sK4 = k1_xboole_0
% 0.37/1.05      | sK6 = k1_xboole_0
% 0.37/1.05      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_3650,c_722]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_28,plain,
% 0.37/1.05      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1,plain,
% 0.37/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 0.37/1.05      inference(cnf_transformation,[],[f39]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_252,plain,( X0 = X0 ),theory(equality) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_279,plain,
% 0.37/1.05      ( k1_xboole_0 = k1_xboole_0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_252]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1172,plain,
% 0.37/1.05      ( sK6 = sK6 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_252]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_265,plain,
% 0.37/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.05      | v1_funct_2(X3,X4,X5)
% 0.37/1.05      | X3 != X0
% 0.37/1.05      | X4 != X1
% 0.37/1.05      | X5 != X2 ),
% 0.37/1.05      theory(equality) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1086,plain,
% 0.37/1.05      ( v1_funct_2(X0,X1,X2)
% 0.37/1.05      | ~ v1_funct_2(sK6,sK4,sK5)
% 0.37/1.05      | X2 != sK5
% 0.37/1.05      | X1 != sK4
% 0.37/1.05      | X0 != sK6 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_265]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1318,plain,
% 0.37/1.05      ( v1_funct_2(sK6,X0,X1)
% 0.37/1.05      | ~ v1_funct_2(sK6,sK4,sK5)
% 0.37/1.05      | X1 != sK5
% 0.37/1.05      | X0 != sK4
% 0.37/1.05      | sK6 != sK6 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_1086]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1697,plain,
% 0.37/1.05      ( v1_funct_2(sK6,sK4,X0)
% 0.37/1.05      | ~ v1_funct_2(sK6,sK4,sK5)
% 0.37/1.05      | X0 != sK5
% 0.37/1.05      | sK4 != sK4
% 0.37/1.05      | sK6 != sK6 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_1318]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1699,plain,
% 0.37/1.05      ( X0 != sK5
% 0.37/1.05      | sK4 != sK4
% 0.37/1.05      | sK6 != sK6
% 0.37/1.05      | v1_funct_2(sK6,sK4,X0) = iProver_top
% 0.37/1.05      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1701,plain,
% 0.37/1.05      ( sK4 != sK4
% 0.37/1.05      | sK6 != sK6
% 0.37/1.05      | k1_xboole_0 != sK5
% 0.37/1.05      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 0.37/1.05      | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_1699]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1698,plain,
% 0.37/1.05      ( sK4 = sK4 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_252]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_253,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2226,plain,
% 0.37/1.05      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_253]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2227,plain,
% 0.37/1.05      ( sK5 != k1_xboole_0
% 0.37/1.05      | k1_xboole_0 = sK5
% 0.37/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_2226]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_0,plain,
% 0.37/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 0.37/1.05      inference(cnf_transformation,[],[f38]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_739,plain,
% 0.37/1.05      ( r2_hidden(X0,X1) != iProver_top
% 0.37/1.05      | v1_xboole_0(X1) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3222,plain,
% 0.37/1.05      ( v1_xboole_0(sK6) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_3217,c_739]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3236,plain,
% 0.37/1.05      ( ~ v1_xboole_0(sK6) ),
% 0.37/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_3222]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_255,plain,
% 0.37/1.05      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.37/1.05      theory(equality) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3524,plain,
% 0.37/1.05      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_255]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3526,plain,
% 0.37/1.05      ( v1_xboole_0(sK6)
% 0.37/1.05      | ~ v1_xboole_0(k1_xboole_0)
% 0.37/1.05      | sK6 != k1_xboole_0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_3524]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4120,plain,
% 0.37/1.05      ( sK4 = k1_xboole_0 ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_3818,c_26,c_28,c_1,c_279,c_1062,c_1172,c_1488,c_1659,
% 0.37/1.05                 c_1701,c_1698,c_2227,c_2259,c_3236,c_3526,c_3570]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3648,plain,
% 0.37/1.05      ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_3644,c_1343]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4124,plain,
% 0.37/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_4120,c_3648]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4125,plain,
% 0.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_4120,c_3650]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_20,plain,
% 0.37/1.05      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.37/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.37/1.05      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 0.37/1.05      inference(cnf_transformation,[],[f74]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_719,plain,
% 0.37/1.05      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 0.37/1.05      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 0.37/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4304,plain,
% 0.37/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 0.37/1.05      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_4125,c_719]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1321,plain,
% 0.37/1.05      ( X0 != sK5
% 0.37/1.05      | X1 != sK4
% 0.37/1.05      | sK6 != sK6
% 0.37/1.05      | v1_funct_2(sK6,X1,X0) = iProver_top
% 0.37/1.05      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 0.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1323,plain,
% 0.37/1.05      ( sK6 != sK6
% 0.37/1.05      | k1_xboole_0 != sK5
% 0.37/1.05      | k1_xboole_0 != sK4
% 0.37/1.05      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 0.37/1.05      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_1321]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1703,plain,
% 0.37/1.05      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_253]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1704,plain,
% 0.37/1.05      ( sK4 != k1_xboole_0
% 0.37/1.05      | k1_xboole_0 = sK4
% 0.37/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_1703]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4624,plain,
% 0.37/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 0.37/1.05      inference(global_propositional_subsumption,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_4304,c_26,c_28,c_1,c_279,c_1062,c_1172,c_1323,c_1488,
% 0.37/1.05                 c_1659,c_1701,c_1698,c_1704,c_2227,c_2259,c_3236,c_3526,
% 0.37/1.05                 c_3570,c_3818]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_4706,plain,
% 0.37/1.05      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 0.37/1.05      inference(light_normalisation,[status(thm)],[c_4124,c_4624]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3529,plain,
% 0.37/1.05      ( ~ v1_xboole_0(X0)
% 0.37/1.05      | v1_xboole_0(k1_relat_1(sK6))
% 0.37/1.05      | k1_relat_1(sK6) != X0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_255]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_3531,plain,
% 0.37/1.05      ( v1_xboole_0(k1_relat_1(sK6))
% 0.37/1.05      | ~ v1_xboole_0(k1_xboole_0)
% 0.37/1.05      | k1_relat_1(sK6) != k1_xboole_0 ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_3529]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2321,plain,
% 0.37/1.05      ( ~ r2_hidden(sK2(sK6,sK3),k1_relat_1(sK6))
% 0.37/1.05      | ~ v1_xboole_0(k1_relat_1(sK6)) ),
% 0.37/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(contradiction,plain,
% 0.37/1.05      ( $false ),
% 0.37/1.05      inference(minisat,
% 0.37/1.05                [status(thm)],
% 0.37/1.05                [c_4706,c_3531,c_2321,c_1660,c_1488,c_1062,c_1,c_26]) ).
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  ------                               Statistics
% 0.37/1.05  
% 0.37/1.05  ------ Selected
% 0.37/1.05  
% 0.37/1.05  total_time:                             0.177
% 0.37/1.05  
%------------------------------------------------------------------------------
