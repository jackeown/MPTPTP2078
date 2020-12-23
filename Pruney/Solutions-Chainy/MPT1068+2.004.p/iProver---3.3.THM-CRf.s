%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:35 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 560 expanded)
%              Number of clauses        :   99 ( 163 expanded)
%              Number of leaves         :   21 ( 183 expanded)
%              Depth                    :   16
%              Number of atoms          :  567 (3960 expanded)
%              Number of equality atoms :  234 (1035 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f58])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f59,f70,f69,f68,f67])).

fof(f113,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f115,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f71])).

fof(f23,axiom,(
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

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f111,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f52])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f116,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3293,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3295,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3320,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5055,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_3320])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3635,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3636,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3635])).

cnf(c_3856,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4007,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | r2_hidden(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3856])).

cnf(c_4008,plain,
    ( m1_subset_1(sK6,sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(c_6908,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5055,c_53,c_38,c_3636,c_4008])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3292,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3298,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7042,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_3298])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3306,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5036,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3292,c_3306])).

cnf(c_7046,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7042,c_5036])).

cnf(c_46,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_49,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_596,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_597,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_599,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_2353,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3678,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_3680,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3678])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4702,plain,
    ( r1_tarski(X0,sK0(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4704,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_4702])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8545,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10152,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7046,c_46,c_49,c_599,c_3680,c_4704,c_8545])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3308,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10156,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10152,c_3308])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_48,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3317,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4174,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_3317])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_353,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_431,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_353])).

cnf(c_3286,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_4394,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4174,c_3286])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3313,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7734,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4394,c_3313])).

cnf(c_14500,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10156,c_48,c_7734])).

cnf(c_14501,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14500])).

cnf(c_14511,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6908,c_14501])).

cnf(c_14684,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3293,c_14511])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3294,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5035,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3294,c_3306])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3305,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4861,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3292,c_3305])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3304,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8132,plain,
    ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_3304])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_11859,plain,
    ( v1_funct_1(X1) != iProver_top
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8132,c_46,c_48,c_49,c_50,c_599,c_3680,c_4704,c_8545])).

cnf(c_11860,plain,
    ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11859])).

cnf(c_11869,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5035,c_11860])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3297,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5631,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_3297])).

cnf(c_51,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6134,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5631,c_51])).

cnf(c_6135,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6134])).

cnf(c_6147,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_6135])).

cnf(c_3820,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X1,X2,sK3,sK1,X0,sK5) = k5_relat_1(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3958,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_4543,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(c_6366,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6147,c_45,c_43,c_42,c_41,c_4543])).

cnf(c_11883,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11869,c_6366])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3296,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5306,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4861,c_3296])).

cnf(c_5379,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5306,c_5035])).

cnf(c_11893,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11883,c_51,c_52,c_5379])).

cnf(c_37,negated_conjecture,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_11896,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_11893,c_37])).

cnf(c_4173,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_3317])).

cnf(c_4382,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_3286])).

cnf(c_4767,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4382,c_3313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14684,c_11896,c_4767])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.42/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/0.99  
% 3.42/0.99  ------  iProver source info
% 3.42/0.99  
% 3.42/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.42/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/0.99  git: non_committed_changes: false
% 3.42/0.99  git: last_make_outside_of_git: false
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/0.99  --bmc1_symbol_reachability              true
% 3.42/0.99  --bmc1_property_lemmas                  false
% 3.42/0.99  --bmc1_k_induction                      false
% 3.42/0.99  --bmc1_non_equiv_states                 false
% 3.42/0.99  --bmc1_deadlock                         false
% 3.42/0.99  --bmc1_ucm                              false
% 3.42/0.99  --bmc1_add_unsat_core                   none
% 3.42/0.99  --bmc1_unsat_core_children              false
% 3.42/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.99  --bmc1_out_stat                         full
% 3.42/0.99  --bmc1_ground_init                      false
% 3.42/0.99  --bmc1_pre_inst_next_state              false
% 3.42/0.99  --bmc1_pre_inst_state                   false
% 3.42/0.99  --bmc1_pre_inst_reach_state             false
% 3.42/0.99  --bmc1_out_unsat_core                   false
% 3.42/0.99  --bmc1_aig_witness_out                  false
% 3.42/0.99  --bmc1_verbose                          false
% 3.42/0.99  --bmc1_dump_clauses_tptp                false
% 3.42/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.99  --bmc1_dump_file                        -
% 3.42/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.99  --bmc1_ucm_extend_mode                  1
% 3.42/0.99  --bmc1_ucm_init_mode                    2
% 3.42/0.99  --bmc1_ucm_cone_mode                    none
% 3.42/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.99  --bmc1_ucm_relax_model                  4
% 3.42/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.99  --bmc1_ucm_layered_model                none
% 3.42/0.99  --bmc1_ucm_max_lemma_size               10
% 3.42/0.99  
% 3.42/0.99  ------ AIG Options
% 3.42/0.99  
% 3.42/0.99  --aig_mode                              false
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation Options
% 3.42/0.99  
% 3.42/0.99  --instantiation_flag                    true
% 3.42/0.99  --inst_sos_flag                         false
% 3.42/0.99  --inst_sos_phase                        true
% 3.42/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel_side                     num_symb
% 3.42/0.99  --inst_solver_per_active                1400
% 3.42/0.99  --inst_solver_calls_frac                1.
% 3.42/0.99  --inst_passive_queue_type               priority_queues
% 3.42/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.99  --inst_passive_queues_freq              [25;2]
% 3.42/0.99  --inst_dismatching                      true
% 3.42/0.99  --inst_eager_unprocessed_to_passive     true
% 3.42/0.99  --inst_prop_sim_given                   true
% 3.42/0.99  --inst_prop_sim_new                     false
% 3.42/0.99  --inst_subs_new                         false
% 3.42/0.99  --inst_eq_res_simp                      false
% 3.42/0.99  --inst_subs_given                       false
% 3.42/0.99  --inst_orphan_elimination               true
% 3.42/0.99  --inst_learning_loop_flag               true
% 3.42/0.99  --inst_learning_start                   3000
% 3.42/0.99  --inst_learning_factor                  2
% 3.42/0.99  --inst_start_prop_sim_after_learn       3
% 3.42/0.99  --inst_sel_renew                        solver
% 3.42/0.99  --inst_lit_activity_flag                true
% 3.42/0.99  --inst_restr_to_given                   false
% 3.42/0.99  --inst_activity_threshold               500
% 3.42/0.99  --inst_out_proof                        true
% 3.42/0.99  
% 3.42/0.99  ------ Resolution Options
% 3.42/0.99  
% 3.42/0.99  --resolution_flag                       true
% 3.42/0.99  --res_lit_sel                           adaptive
% 3.42/0.99  --res_lit_sel_side                      none
% 3.42/0.99  --res_ordering                          kbo
% 3.42/0.99  --res_to_prop_solver                    active
% 3.42/0.99  --res_prop_simpl_new                    false
% 3.42/0.99  --res_prop_simpl_given                  true
% 3.42/0.99  --res_passive_queue_type                priority_queues
% 3.42/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.99  --res_passive_queues_freq               [15;5]
% 3.42/0.99  --res_forward_subs                      full
% 3.42/0.99  --res_backward_subs                     full
% 3.42/0.99  --res_forward_subs_resolution           true
% 3.42/0.99  --res_backward_subs_resolution          true
% 3.42/0.99  --res_orphan_elimination                true
% 3.42/0.99  --res_time_limit                        2.
% 3.42/0.99  --res_out_proof                         true
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Options
% 3.42/0.99  
% 3.42/0.99  --superposition_flag                    true
% 3.42/0.99  --sup_passive_queue_type                priority_queues
% 3.42/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.99  --demod_completeness_check              fast
% 3.42/0.99  --demod_use_ground                      true
% 3.42/0.99  --sup_to_prop_solver                    passive
% 3.42/0.99  --sup_prop_simpl_new                    true
% 3.42/0.99  --sup_prop_simpl_given                  true
% 3.42/0.99  --sup_fun_splitting                     false
% 3.42/0.99  --sup_smt_interval                      50000
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Simplification Setup
% 3.42/0.99  
% 3.42/0.99  --sup_indices_passive                   []
% 3.42/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_full_bw                           [BwDemod]
% 3.42/0.99  --sup_immed_triv                        [TrivRules]
% 3.42/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_immed_bw_main                     []
% 3.42/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  
% 3.42/0.99  ------ Combination Options
% 3.42/0.99  
% 3.42/0.99  --comb_res_mult                         3
% 3.42/0.99  --comb_sup_mult                         2
% 3.42/0.99  --comb_inst_mult                        10
% 3.42/0.99  
% 3.42/0.99  ------ Debug Options
% 3.42/0.99  
% 3.42/0.99  --dbg_backtrace                         false
% 3.42/0.99  --dbg_dump_prop_clauses                 false
% 3.42/0.99  --dbg_dump_prop_clauses_file            -
% 3.42/0.99  --dbg_out_stat                          false
% 3.42/0.99  ------ Parsing...
% 3.42/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/0.99  ------ Proving...
% 3.42/0.99  ------ Problem Properties 
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  clauses                                 43
% 3.42/0.99  conjectures                             10
% 3.42/0.99  EPR                                     15
% 3.42/0.99  Horn                                    35
% 3.42/0.99  unary                                   12
% 3.42/0.99  binary                                  11
% 3.42/0.99  lits                                    109
% 3.42/0.99  lits eq                                 21
% 3.42/0.99  fd_pure                                 0
% 3.42/0.99  fd_pseudo                               0
% 3.42/0.99  fd_cond                                 5
% 3.42/0.99  fd_pseudo_cond                          0
% 3.42/0.99  AC symbols                              0
% 3.42/0.99  
% 3.42/0.99  ------ Schedule dynamic 5 is on 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  Current options:
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/0.99  --bmc1_symbol_reachability              true
% 3.42/0.99  --bmc1_property_lemmas                  false
% 3.42/0.99  --bmc1_k_induction                      false
% 3.42/0.99  --bmc1_non_equiv_states                 false
% 3.42/0.99  --bmc1_deadlock                         false
% 3.42/0.99  --bmc1_ucm                              false
% 3.42/0.99  --bmc1_add_unsat_core                   none
% 3.42/0.99  --bmc1_unsat_core_children              false
% 3.42/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.99  --bmc1_out_stat                         full
% 3.42/0.99  --bmc1_ground_init                      false
% 3.42/0.99  --bmc1_pre_inst_next_state              false
% 3.42/0.99  --bmc1_pre_inst_state                   false
% 3.42/0.99  --bmc1_pre_inst_reach_state             false
% 3.42/0.99  --bmc1_out_unsat_core                   false
% 3.42/0.99  --bmc1_aig_witness_out                  false
% 3.42/0.99  --bmc1_verbose                          false
% 3.42/0.99  --bmc1_dump_clauses_tptp                false
% 3.42/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.99  --bmc1_dump_file                        -
% 3.42/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.99  --bmc1_ucm_extend_mode                  1
% 3.42/0.99  --bmc1_ucm_init_mode                    2
% 3.42/0.99  --bmc1_ucm_cone_mode                    none
% 3.42/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.99  --bmc1_ucm_relax_model                  4
% 3.42/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.99  --bmc1_ucm_layered_model                none
% 3.42/0.99  --bmc1_ucm_max_lemma_size               10
% 3.42/0.99  
% 3.42/0.99  ------ AIG Options
% 3.42/0.99  
% 3.42/0.99  --aig_mode                              false
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation Options
% 3.42/0.99  
% 3.42/0.99  --instantiation_flag                    true
% 3.42/0.99  --inst_sos_flag                         false
% 3.42/0.99  --inst_sos_phase                        true
% 3.42/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel_side                     none
% 3.42/0.99  --inst_solver_per_active                1400
% 3.42/0.99  --inst_solver_calls_frac                1.
% 3.42/0.99  --inst_passive_queue_type               priority_queues
% 3.42/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.99  --inst_passive_queues_freq              [25;2]
% 3.42/0.99  --inst_dismatching                      true
% 3.42/0.99  --inst_eager_unprocessed_to_passive     true
% 3.42/0.99  --inst_prop_sim_given                   true
% 3.42/0.99  --inst_prop_sim_new                     false
% 3.42/0.99  --inst_subs_new                         false
% 3.42/0.99  --inst_eq_res_simp                      false
% 3.42/0.99  --inst_subs_given                       false
% 3.42/0.99  --inst_orphan_elimination               true
% 3.42/0.99  --inst_learning_loop_flag               true
% 3.42/0.99  --inst_learning_start                   3000
% 3.42/0.99  --inst_learning_factor                  2
% 3.42/0.99  --inst_start_prop_sim_after_learn       3
% 3.42/0.99  --inst_sel_renew                        solver
% 3.42/0.99  --inst_lit_activity_flag                true
% 3.42/0.99  --inst_restr_to_given                   false
% 3.42/0.99  --inst_activity_threshold               500
% 3.42/0.99  --inst_out_proof                        true
% 3.42/0.99  
% 3.42/0.99  ------ Resolution Options
% 3.42/0.99  
% 3.42/0.99  --resolution_flag                       false
% 3.42/0.99  --res_lit_sel                           adaptive
% 3.42/0.99  --res_lit_sel_side                      none
% 3.42/0.99  --res_ordering                          kbo
% 3.42/0.99  --res_to_prop_solver                    active
% 3.42/0.99  --res_prop_simpl_new                    false
% 3.42/0.99  --res_prop_simpl_given                  true
% 3.42/0.99  --res_passive_queue_type                priority_queues
% 3.42/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.99  --res_passive_queues_freq               [15;5]
% 3.42/0.99  --res_forward_subs                      full
% 3.42/0.99  --res_backward_subs                     full
% 3.42/0.99  --res_forward_subs_resolution           true
% 3.42/0.99  --res_backward_subs_resolution          true
% 3.42/0.99  --res_orphan_elimination                true
% 3.42/0.99  --res_time_limit                        2.
% 3.42/0.99  --res_out_proof                         true
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Options
% 3.42/0.99  
% 3.42/0.99  --superposition_flag                    true
% 3.42/0.99  --sup_passive_queue_type                priority_queues
% 3.42/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.99  --demod_completeness_check              fast
% 3.42/0.99  --demod_use_ground                      true
% 3.42/0.99  --sup_to_prop_solver                    passive
% 3.42/0.99  --sup_prop_simpl_new                    true
% 3.42/0.99  --sup_prop_simpl_given                  true
% 3.42/0.99  --sup_fun_splitting                     false
% 3.42/0.99  --sup_smt_interval                      50000
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Simplification Setup
% 3.42/0.99  
% 3.42/0.99  --sup_indices_passive                   []
% 3.42/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_full_bw                           [BwDemod]
% 3.42/0.99  --sup_immed_triv                        [TrivRules]
% 3.42/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_immed_bw_main                     []
% 3.42/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  
% 3.42/0.99  ------ Combination Options
% 3.42/0.99  
% 3.42/0.99  --comb_res_mult                         3
% 3.42/0.99  --comb_sup_mult                         2
% 3.42/0.99  --comb_inst_mult                        10
% 3.42/0.99  
% 3.42/0.99  ------ Debug Options
% 3.42/0.99  
% 3.42/0.99  --dbg_backtrace                         false
% 3.42/0.99  --dbg_dump_prop_clauses                 false
% 3.42/0.99  --dbg_dump_prop_clauses_file            -
% 3.42/0.99  --dbg_out_stat                          false
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  ------ Proving...
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  % SZS status Theorem for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  fof(f25,conjecture,(
% 3.42/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f26,negated_conjecture,(
% 3.42/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.42/0.99    inference(negated_conjecture,[],[f25])).
% 3.42/0.99  
% 3.42/0.99  fof(f58,plain,(
% 3.42/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.42/0.99    inference(ennf_transformation,[],[f26])).
% 3.42/0.99  
% 3.42/0.99  fof(f59,plain,(
% 3.42/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.42/0.99    inference(flattening,[],[f58])).
% 3.42/0.99  
% 3.42/0.99  fof(f70,plain,(
% 3.42/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f69,plain,(
% 3.42/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f68,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f67,plain,(
% 3.42/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f71,plain,(
% 3.42/0.99    (((k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 3.42/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f59,f70,f69,f68,f67])).
% 3.42/0.99  
% 3.42/0.99  fof(f113,plain,(
% 3.42/0.99    v1_funct_1(sK5)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f115,plain,(
% 3.42/0.99    m1_subset_1(sK6,sK2)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f4,axiom,(
% 3.42/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f30,plain,(
% 3.42/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.42/0.99    inference(ennf_transformation,[],[f4])).
% 3.42/0.99  
% 3.42/0.99  fof(f64,plain,(
% 3.42/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.42/0.99    inference(nnf_transformation,[],[f30])).
% 3.42/0.99  
% 3.42/0.99  fof(f76,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f64])).
% 3.42/0.99  
% 3.42/0.99  fof(f117,plain,(
% 3.42/0.99    k1_xboole_0 != sK2),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f2,axiom,(
% 3.42/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f28,plain,(
% 3.42/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f2])).
% 3.42/0.99  
% 3.42/0.99  fof(f74,plain,(
% 3.42/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f28])).
% 3.42/0.99  
% 3.42/0.99  fof(f112,plain,(
% 3.42/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f23,axiom,(
% 3.42/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f54,plain,(
% 3.42/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.99    inference(ennf_transformation,[],[f23])).
% 3.42/0.99  
% 3.42/0.99  fof(f55,plain,(
% 3.42/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.99    inference(flattening,[],[f54])).
% 3.42/0.99  
% 3.42/0.99  fof(f66,plain,(
% 3.42/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.99    inference(nnf_transformation,[],[f55])).
% 3.42/0.99  
% 3.42/0.99  fof(f102,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f66])).
% 3.42/0.99  
% 3.42/0.99  fof(f19,axiom,(
% 3.42/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f48,plain,(
% 3.42/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.99    inference(ennf_transformation,[],[f19])).
% 3.42/0.99  
% 3.42/0.99  fof(f96,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f48])).
% 3.42/0.99  
% 3.42/0.99  fof(f109,plain,(
% 3.42/0.99    ~v1_xboole_0(sK3)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f111,plain,(
% 3.42/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f1,axiom,(
% 3.42/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f60,plain,(
% 3.42/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.42/0.99    inference(nnf_transformation,[],[f1])).
% 3.42/0.99  
% 3.42/0.99  fof(f61,plain,(
% 3.42/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.42/0.99    inference(rectify,[],[f60])).
% 3.42/0.99  
% 3.42/0.99  fof(f62,plain,(
% 3.42/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f63,plain,(
% 3.42/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.42/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).
% 3.42/0.99  
% 3.42/0.99  fof(f73,plain,(
% 3.42/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f63])).
% 3.42/0.99  
% 3.42/0.99  fof(f17,axiom,(
% 3.42/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f46,plain,(
% 3.42/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.42/0.99    inference(ennf_transformation,[],[f17])).
% 3.42/0.99  
% 3.42/0.99  fof(f94,plain,(
% 3.42/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f46])).
% 3.42/0.99  
% 3.42/0.99  fof(f6,axiom,(
% 3.42/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f65,plain,(
% 3.42/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.42/0.99    inference(nnf_transformation,[],[f6])).
% 3.42/0.99  
% 3.42/0.99  fof(f81,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f65])).
% 3.42/0.99  
% 3.42/0.99  fof(f5,axiom,(
% 3.42/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f80,plain,(
% 3.42/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f5])).
% 3.42/0.99  
% 3.42/0.99  fof(f16,axiom,(
% 3.42/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f44,plain,(
% 3.42/0.99    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/0.99    inference(ennf_transformation,[],[f16])).
% 3.42/0.99  
% 3.42/0.99  fof(f45,plain,(
% 3.42/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.99    inference(flattening,[],[f44])).
% 3.42/0.99  
% 3.42/0.99  fof(f93,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f45])).
% 3.42/0.99  
% 3.42/0.99  fof(f110,plain,(
% 3.42/0.99    v1_funct_1(sK4)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f8,axiom,(
% 3.42/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f33,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f8])).
% 3.42/0.99  
% 3.42/0.99  fof(f84,plain,(
% 3.42/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f33])).
% 3.42/0.99  
% 3.42/0.99  fof(f82,plain,(
% 3.42/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f65])).
% 3.42/0.99  
% 3.42/0.99  fof(f10,axiom,(
% 3.42/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f87,plain,(
% 3.42/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f10])).
% 3.42/0.99  
% 3.42/0.99  fof(f114,plain,(
% 3.42/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f20,axiom,(
% 3.42/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f49,plain,(
% 3.42/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.99    inference(ennf_transformation,[],[f20])).
% 3.42/0.99  
% 3.42/0.99  fof(f97,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f49])).
% 3.42/0.99  
% 3.42/0.99  fof(f22,axiom,(
% 3.42/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f52,plain,(
% 3.42/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.42/0.99    inference(ennf_transformation,[],[f22])).
% 3.42/0.99  
% 3.42/0.99  fof(f53,plain,(
% 3.42/0.99    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.42/0.99    inference(flattening,[],[f52])).
% 3.42/0.99  
% 3.42/0.99  fof(f101,plain,(
% 3.42/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f53])).
% 3.42/0.99  
% 3.42/0.99  fof(f24,axiom,(
% 3.42/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f56,plain,(
% 3.42/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.42/0.99    inference(ennf_transformation,[],[f24])).
% 3.42/0.99  
% 3.42/0.99  fof(f57,plain,(
% 3.42/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.42/0.99    inference(flattening,[],[f56])).
% 3.42/0.99  
% 3.42/0.99  fof(f108,plain,(
% 3.42/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f57])).
% 3.42/0.99  
% 3.42/0.99  fof(f116,plain,(
% 3.42/0.99    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  fof(f118,plain,(
% 3.42/0.99    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 3.42/0.99    inference(cnf_transformation,[],[f71])).
% 3.42/0.99  
% 3.42/0.99  cnf(c_42,negated_conjecture,
% 3.42/0.99      ( v1_funct_1(sK5) ),
% 3.42/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3293,plain,
% 3.42/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_40,negated_conjecture,
% 3.42/0.99      ( m1_subset_1(sK6,sK2) ),
% 3.42/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3295,plain,
% 3.42/0.99      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.42/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3320,plain,
% 3.42/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.42/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.42/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5055,plain,
% 3.42/0.99      ( r2_hidden(sK6,sK2) = iProver_top
% 3.42/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3295,c_3320]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_53,plain,
% 3.42/0.99      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_38,negated_conjecture,
% 3.42/0.99      ( k1_xboole_0 != sK2 ),
% 3.42/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2,plain,
% 3.42/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.42/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3635,plain,
% 3.42/0.99      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3636,plain,
% 3.42/0.99      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_3635]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3856,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK2) | v1_xboole_0(sK2) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4007,plain,
% 3.42/0.99      ( ~ m1_subset_1(sK6,sK2) | r2_hidden(sK6,sK2) | v1_xboole_0(sK2) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3856]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4008,plain,
% 3.42/0.99      ( m1_subset_1(sK6,sK2) != iProver_top
% 3.42/0.99      | r2_hidden(sK6,sK2) = iProver_top
% 3.42/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_4007]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6908,plain,
% 3.42/0.99      ( r2_hidden(sK6,sK2) = iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5055,c_53,c_38,c_3636,c_4008]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_43,negated_conjecture,
% 3.42/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.42/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3292,plain,
% 3.42/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_35,plain,
% 3.42/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.42/0.99      | k1_xboole_0 = X2 ),
% 3.42/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3298,plain,
% 3.42/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.42/0.99      | k1_xboole_0 = X1
% 3.42/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7042,plain,
% 3.42/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.42/0.99      | sK3 = k1_xboole_0
% 3.42/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3292,c_3298]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_24,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3306,plain,
% 3.42/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5036,plain,
% 3.42/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3292,c_3306]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7046,plain,
% 3.42/0.99      ( k1_relat_1(sK4) = sK2
% 3.42/0.99      | sK3 = k1_xboole_0
% 3.42/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_7042,c_5036]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_46,negated_conjecture,
% 3.42/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.42/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_44,negated_conjecture,
% 3.42/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.42/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_49,plain,
% 3.42/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_0,plain,
% 3.42/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_22,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_596,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X2) | X0 != X2 | sK0(X2) != X1 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_597,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,sK0(X0)) | v1_xboole_0(X0) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_596]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_599,plain,
% 3.42/0.99      ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 3.42/0.99      | v1_xboole_0(k1_xboole_0) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_597]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2353,plain,
% 3.42/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.42/0.99      theory(equality) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3678,plain,
% 3.42/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2353]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3680,plain,
% 3.42/0.99      ( v1_xboole_0(sK3)
% 3.42/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.42/0.99      | sK3 != k1_xboole_0 ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3678]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_10,plain,
% 3.42/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4702,plain,
% 3.42/0.99      ( r1_tarski(X0,sK0(X0)) | ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X0))) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4704,plain,
% 3.42/0.99      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 3.42/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4702]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_8,plain,
% 3.42/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_8545,plain,
% 3.42/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_10152,plain,
% 3.42/0.99      ( k1_relat_1(sK4) = sK2 ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_7046,c_46,c_49,c_599,c_3680,c_4704,c_8545]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_21,plain,
% 3.42/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.42/0.99      | ~ v1_funct_1(X2)
% 3.42/0.99      | ~ v1_funct_1(X1)
% 3.42/0.99      | ~ v1_relat_1(X2)
% 3.42/0.99      | ~ v1_relat_1(X1)
% 3.42/0.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3308,plain,
% 3.42/0.99      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.42/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.42/0.99      | v1_funct_1(X1) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(X1) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_10156,plain,
% 3.42/0.99      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.42/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_funct_1(sK4) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_10152,c_3308]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_45,negated_conjecture,
% 3.42/0.99      ( v1_funct_1(sK4) ),
% 3.42/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_48,plain,
% 3.42/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3317,plain,
% 3.42/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.42/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4174,plain,
% 3.42/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3292,c_3317]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.42/0.99      | ~ v1_relat_1(X1)
% 3.42/0.99      | v1_relat_1(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_9,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_353,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.42/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_431,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.42/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_353]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3286,plain,
% 3.42/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.42/0.99      | v1_relat_1(X1) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4394,plain,
% 3.42/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.42/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_4174,c_3286]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_15,plain,
% 3.42/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3313,plain,
% 3.42/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7734,plain,
% 3.42/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.42/0.99      inference(forward_subsumption_resolution,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4394,c_3313]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_14500,plain,
% 3.42/0.99      ( v1_relat_1(X0) != iProver_top
% 3.42/0.99      | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.42/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_10156,c_48,c_7734]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_14501,plain,
% 3.42/0.99      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.42/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_14500]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_14511,plain,
% 3.42/0.99      ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_6908,c_14501]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_14684,plain,
% 3.42/0.99      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 3.42/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3293,c_14511]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_41,negated_conjecture,
% 3.42/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.42/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3294,plain,
% 3.42/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5035,plain,
% 3.42/0.99      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3294,c_3306]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_25,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3305,plain,
% 3.42/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4861,plain,
% 3.42/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3292,c_3305]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_29,plain,
% 3.42/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.42/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 3.42/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | ~ v1_funct_1(X4)
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
% 3.42/0.99      | k1_xboole_0 = X2 ),
% 3.42/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3304,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 3.42/0.99      | k1_xboole_0 = X1
% 3.42/0.99      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.42/0.99      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.42/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.42/0.99      | v1_funct_1(X3) != iProver_top
% 3.42/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_8132,plain,
% 3.42/0.99      ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 3.42/0.99      | sK3 = k1_xboole_0
% 3.42/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.42/0.99      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 3.42/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 3.42/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.42/0.99      | v1_funct_1(X1) != iProver_top
% 3.42/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_4861,c_3304]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_50,plain,
% 3.42/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11859,plain,
% 3.42/0.99      ( v1_funct_1(X1) != iProver_top
% 3.42/0.99      | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 3.42/0.99      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 3.42/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_8132,c_46,c_48,c_49,c_50,c_599,c_3680,c_4704,c_8545]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11860,plain,
% 3.42/0.99      ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 3.42/0.99      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 3.42/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 3.42/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_11859]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11869,plain,
% 3.42/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
% 3.42/0.99      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.42/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.42/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_5035,c_11860]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_36,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.42/0.99      | ~ v1_funct_1(X3)
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3297,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.42/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.42/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X4) != iProver_top
% 3.42/0.99      | v1_funct_1(X5) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5631,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top
% 3.42/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3294,c_3297]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_51,plain,
% 3.42/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6134,plain,
% 3.42/0.99      ( v1_funct_1(X2) != iProver_top
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5631,c_51]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6135,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_6134]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6147,plain,
% 3.42/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.42/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3292,c_6135]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3820,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | ~ v1_funct_1(sK5)
% 3.42/0.99      | k1_partfun1(X1,X2,sK3,sK1,X0,sK5) = k5_relat_1(X0,sK5) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3958,plain,
% 3.42/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.42/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.42/0.99      | ~ v1_funct_1(sK4)
% 3.42/0.99      | ~ v1_funct_1(sK5)
% 3.42/0.99      | k1_partfun1(X0,X1,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3820]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4543,plain,
% 3.42/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.42/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.42/0.99      | ~ v1_funct_1(sK4)
% 3.42/0.99      | ~ v1_funct_1(sK5)
% 3.42/0.99      | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3958]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6366,plain,
% 3.42/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_6147,c_45,c_43,c_42,c_41,c_4543]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11883,plain,
% 3.42/0.99      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.42/0.99      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.42/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.42/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_11869,c_6366]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_52,plain,
% 3.42/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_39,negated_conjecture,
% 3.42/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3296,plain,
% 3.42/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5306,plain,
% 3.42/0.99      ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_4861,c_3296]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5379,plain,
% 3.42/0.99      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_5306,c_5035]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11893,plain,
% 3.42/0.99      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_11883,c_51,c_52,c_5379]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_37,negated_conjecture,
% 3.42/0.99      ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 3.42/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11896,plain,
% 3.42/0.99      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_11893,c_37]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4173,plain,
% 3.42/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3294,c_3317]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4382,plain,
% 3.42/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 3.42/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_4173,c_3286]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4767,plain,
% 3.42/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.42/0.99      inference(forward_subsumption_resolution,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4382,c_3313]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(contradiction,plain,
% 3.42/0.99      ( $false ),
% 3.42/0.99      inference(minisat,[status(thm)],[c_14684,c_11896,c_4767]) ).
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  ------                               Statistics
% 3.42/0.99  
% 3.42/0.99  ------ General
% 3.42/0.99  
% 3.42/0.99  abstr_ref_over_cycles:                  0
% 3.42/0.99  abstr_ref_under_cycles:                 0
% 3.42/0.99  gc_basic_clause_elim:                   0
% 3.42/0.99  forced_gc_time:                         0
% 3.42/0.99  parsing_time:                           0.01
% 3.42/0.99  unif_index_cands_time:                  0.
% 3.42/0.99  unif_index_add_time:                    0.
% 3.42/0.99  orderings_time:                         0.
% 3.42/0.99  out_proof_time:                         0.012
% 3.42/0.99  total_time:                             0.369
% 3.42/0.99  num_of_symbols:                         59
% 3.42/0.99  num_of_terms:                           13798
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing
% 3.42/0.99  
% 3.42/0.99  num_of_splits:                          0
% 3.42/0.99  num_of_split_atoms:                     0
% 3.42/0.99  num_of_reused_defs:                     0
% 3.42/0.99  num_eq_ax_congr_red:                    41
% 3.42/0.99  num_of_sem_filtered_clauses:            1
% 3.42/0.99  num_of_subtypes:                        0
% 3.42/0.99  monotx_restored_types:                  0
% 3.42/0.99  sat_num_of_epr_types:                   0
% 3.42/0.99  sat_num_of_non_cyclic_types:            0
% 3.42/0.99  sat_guarded_non_collapsed_types:        0
% 3.42/0.99  num_pure_diseq_elim:                    0
% 3.42/0.99  simp_replaced_by:                       0
% 3.42/0.99  res_preprocessed:                       208
% 3.42/0.99  prep_upred:                             0
% 3.42/0.99  prep_unflattend:                        168
% 3.42/0.99  smt_new_axioms:                         0
% 3.42/0.99  pred_elim_cands:                        7
% 3.42/0.99  pred_elim:                              1
% 3.42/0.99  pred_elim_cl:                           1
% 3.42/0.99  pred_elim_cycles:                       7
% 3.42/0.99  merged_defs:                            8
% 3.42/0.99  merged_defs_ncl:                        0
% 3.42/0.99  bin_hyper_res:                          9
% 3.42/0.99  prep_cycles:                            4
% 3.42/0.99  pred_elim_time:                         0.028
% 3.42/0.99  splitting_time:                         0.
% 3.42/0.99  sem_filter_time:                        0.
% 3.42/0.99  monotx_time:                            0.
% 3.42/0.99  subtype_inf_time:                       0.
% 3.42/0.99  
% 3.42/0.99  ------ Problem properties
% 3.42/0.99  
% 3.42/0.99  clauses:                                43
% 3.42/0.99  conjectures:                            10
% 3.42/0.99  epr:                                    15
% 3.42/0.99  horn:                                   35
% 3.42/0.99  ground:                                 10
% 3.42/0.99  unary:                                  12
% 3.42/0.99  binary:                                 11
% 3.42/0.99  lits:                                   109
% 3.42/0.99  lits_eq:                                21
% 3.42/0.99  fd_pure:                                0
% 3.42/0.99  fd_pseudo:                              0
% 3.42/0.99  fd_cond:                                5
% 3.42/0.99  fd_pseudo_cond:                         0
% 3.42/0.99  ac_symbols:                             0
% 3.42/0.99  
% 3.42/0.99  ------ Propositional Solver
% 3.42/0.99  
% 3.42/0.99  prop_solver_calls:                      28
% 3.42/0.99  prop_fast_solver_calls:                 1838
% 3.42/0.99  smt_solver_calls:                       0
% 3.42/0.99  smt_fast_solver_calls:                  0
% 3.42/0.99  prop_num_of_clauses:                    4843
% 3.42/0.99  prop_preprocess_simplified:             14518
% 3.42/0.99  prop_fo_subsumed:                       56
% 3.42/0.99  prop_solver_time:                       0.
% 3.42/0.99  smt_solver_time:                        0.
% 3.42/0.99  smt_fast_solver_time:                   0.
% 3.42/0.99  prop_fast_solver_time:                  0.
% 3.42/0.99  prop_unsat_core_time:                   0.
% 3.42/0.99  
% 3.42/0.99  ------ QBF
% 3.42/0.99  
% 3.42/0.99  qbf_q_res:                              0
% 3.42/0.99  qbf_num_tautologies:                    0
% 3.42/0.99  qbf_prep_cycles:                        0
% 3.42/0.99  
% 3.42/0.99  ------ BMC1
% 3.42/0.99  
% 3.42/0.99  bmc1_current_bound:                     -1
% 3.42/0.99  bmc1_last_solved_bound:                 -1
% 3.42/0.99  bmc1_unsat_core_size:                   -1
% 3.42/0.99  bmc1_unsat_core_parents_size:           -1
% 3.42/0.99  bmc1_merge_next_fun:                    0
% 3.42/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation
% 3.42/0.99  
% 3.42/0.99  inst_num_of_clauses:                    1368
% 3.42/0.99  inst_num_in_passive:                    456
% 3.42/0.99  inst_num_in_active:                     566
% 3.42/0.99  inst_num_in_unprocessed:                360
% 3.42/0.99  inst_num_of_loops:                      710
% 3.42/0.99  inst_num_of_learning_restarts:          0
% 3.42/0.99  inst_num_moves_active_passive:          142
% 3.42/0.99  inst_lit_activity:                      0
% 3.42/0.99  inst_lit_activity_moves:                0
% 3.42/0.99  inst_num_tautologies:                   0
% 3.42/0.99  inst_num_prop_implied:                  0
% 3.42/0.99  inst_num_existing_simplified:           0
% 3.42/0.99  inst_num_eq_res_simplified:             0
% 3.42/0.99  inst_num_child_elim:                    0
% 3.42/0.99  inst_num_of_dismatching_blockings:      730
% 3.42/0.99  inst_num_of_non_proper_insts:           1259
% 3.42/0.99  inst_num_of_duplicates:                 0
% 3.42/0.99  inst_inst_num_from_inst_to_res:         0
% 3.42/0.99  inst_dismatching_checking_time:         0.
% 3.42/0.99  
% 3.42/0.99  ------ Resolution
% 3.42/0.99  
% 3.42/0.99  res_num_of_clauses:                     0
% 3.42/0.99  res_num_in_passive:                     0
% 3.42/0.99  res_num_in_active:                      0
% 3.42/0.99  res_num_of_loops:                       212
% 3.42/0.99  res_forward_subset_subsumed:            130
% 3.42/0.99  res_backward_subset_subsumed:           40
% 3.42/0.99  res_forward_subsumed:                   0
% 3.42/0.99  res_backward_subsumed:                  0
% 3.42/0.99  res_forward_subsumption_resolution:     1
% 3.42/0.99  res_backward_subsumption_resolution:    0
% 3.42/0.99  res_clause_to_clause_subsumption:       530
% 3.42/0.99  res_orphan_elimination:                 0
% 3.42/0.99  res_tautology_del:                      87
% 3.42/0.99  res_num_eq_res_simplified:              0
% 3.42/0.99  res_num_sel_changes:                    0
% 3.42/0.99  res_moves_from_active_to_pass:          0
% 3.42/0.99  
% 3.42/0.99  ------ Superposition
% 3.42/0.99  
% 3.42/0.99  sup_time_total:                         0.
% 3.42/0.99  sup_time_generating:                    0.
% 3.42/0.99  sup_time_sim_full:                      0.
% 3.42/0.99  sup_time_sim_immed:                     0.
% 3.42/0.99  
% 3.42/0.99  sup_num_of_clauses:                     226
% 3.42/0.99  sup_num_in_active:                      132
% 3.42/0.99  sup_num_in_passive:                     94
% 3.42/0.99  sup_num_of_loops:                       140
% 3.42/0.99  sup_fw_superposition:                   141
% 3.42/0.99  sup_bw_superposition:                   96
% 3.42/0.99  sup_immediate_simplified:               29
% 3.42/0.99  sup_given_eliminated:                   0
% 3.42/0.99  comparisons_done:                       0
% 3.42/0.99  comparisons_avoided:                    5
% 3.42/0.99  
% 3.42/0.99  ------ Simplifications
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  sim_fw_subset_subsumed:                 8
% 3.42/0.99  sim_bw_subset_subsumed:                 4
% 3.42/0.99  sim_fw_subsumed:                        3
% 3.42/0.99  sim_bw_subsumed:                        0
% 3.42/0.99  sim_fw_subsumption_res:                 6
% 3.42/0.99  sim_bw_subsumption_res:                 0
% 3.42/0.99  sim_tautology_del:                      11
% 3.42/0.99  sim_eq_tautology_del:                   3
% 3.42/0.99  sim_eq_res_simp:                        0
% 3.42/0.99  sim_fw_demodulated:                     5
% 3.42/0.99  sim_bw_demodulated:                     5
% 3.42/0.99  sim_light_normalised:                   20
% 3.42/0.99  sim_joinable_taut:                      0
% 3.42/0.99  sim_joinable_simp:                      0
% 3.42/0.99  sim_ac_normalised:                      0
% 3.42/0.99  sim_smt_subsumption:                    0
% 3.42/0.99  
%------------------------------------------------------------------------------
