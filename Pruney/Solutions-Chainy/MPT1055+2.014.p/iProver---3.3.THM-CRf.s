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
% DateTime   : Thu Dec  3 12:09:10 EST 2020

% Result     : Theorem 47.87s
% Output     : CNFRefutation 47.87s
% Verified   : 
% Statistics : Number of formulae       :  170 (1131 expanded)
%              Number of clauses        :   94 ( 326 expanded)
%              Number of leaves         :   25 ( 341 expanded)
%              Depth                    :   20
%              Number of atoms          :  523 (7967 expanded)
%              Number of equality atoms :  140 ( 416 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5))
          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5) )
        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5))
          | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(X1)) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ? [X4] :
            ( ( ~ r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4))
              | ~ r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4) )
            & ( r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4))
              | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                    | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(X1)) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4))
                  | ~ r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4))
                  | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(X1)) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4))
                      | ~ r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4))
                      | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_2(X2,X0,sK2)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X2,sK1,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
      | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) )
    & ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
      | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f62,f67,f66,f65,f64,f63])).

fof(f105,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f104,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f57])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,
    ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,
    ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1427,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1437,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3091,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1427,c_1437])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1434,plain,
    ( k8_relset_1(X0,X1,X2,X1) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3892,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1434])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_654,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2083,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_2085,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_7,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1452,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1450,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3050,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1450])).

cnf(c_3077,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3050])).

cnf(c_3079,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_3946,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3892])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4495,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4499,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4495])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6735,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | ~ r1_tarski(X0,sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6737,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6735])).

cnf(c_16566,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3892,c_39,c_38,c_37,c_2085,c_3079,c_3946,c_4499,c_6737])).

cnf(c_16569,plain,
    ( k10_relat_1(sK3,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3091,c_16566])).

cnf(c_17,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1443,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_200284,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16569,c_1443])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1430,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6880,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3091,c_1430])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1438,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3548,plain,
    ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1427,c_1438])).

cnf(c_13366,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6880,c_3548])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1455,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13372,plain,
    ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13366,c_1455])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1448,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2424,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1448])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1454,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6303,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0(k1_zfmisc_1(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_1454])).

cnf(c_10150,plain,
    ( k2_xboole_0(sK0(k1_zfmisc_1(X0)),X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6303,c_1455])).

cnf(c_13413,plain,
    ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
    | k2_xboole_0(sK0(k1_zfmisc_1(sK4)),k10_relat_1(sK3,sK5)) = k10_relat_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_13372,c_10150])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_248])).

cnf(c_1959,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_36])).

cnf(c_2224,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_319,c_1959])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2448,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2224,c_15])).

cnf(c_2449,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_13414,plain,
    ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
    | r1_tarski(k10_relat_1(sK3,sK5),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13372,c_1454])).

cnf(c_23330,plain,
    ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
    | r1_tarski(sK4,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_13414])).

cnf(c_19,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1441,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13374,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13366,c_1441])).

cnf(c_39155,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13374,c_43,c_2449])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1431,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6879,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3091,c_1431])).

cnf(c_15608,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6879,c_3548])).

cnf(c_39170,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39155,c_15608])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1442,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1444,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4802,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_1454])).

cnf(c_27487,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_4802])).

cnf(c_59281,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39155,c_27487])).

cnf(c_126041,plain,
    ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13413,c_43,c_2449,c_23330,c_39170,c_59281])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1456,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_126044,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_126041,c_1456])).

cnf(c_126294,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,X0)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_126044,c_1441])).

cnf(c_198496,plain,
    ( r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_126294,c_43,c_2449,c_39170,c_59281])).

cnf(c_2013,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2653,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_12439,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(sK3))
    | ~ r1_tarski(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_2653])).

cnf(c_12444,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK4,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12439])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1957,plain,
    ( r1_tarski(sK4,sK1) ),
    inference(resolution,[status(thm)],[c_11,c_35])).

cnf(c_1958,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1957])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_200284,c_198496,c_12444,c_2449,c_1958])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 47.87/6.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.87/6.50  
% 47.87/6.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.87/6.50  
% 47.87/6.50  ------  iProver source info
% 47.87/6.50  
% 47.87/6.50  git: date: 2020-06-30 10:37:57 +0100
% 47.87/6.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.87/6.50  git: non_committed_changes: false
% 47.87/6.50  git: last_make_outside_of_git: false
% 47.87/6.50  
% 47.87/6.50  ------ 
% 47.87/6.50  
% 47.87/6.50  ------ Input Options
% 47.87/6.50  
% 47.87/6.50  --out_options                           all
% 47.87/6.50  --tptp_safe_out                         true
% 47.87/6.50  --problem_path                          ""
% 47.87/6.50  --include_path                          ""
% 47.87/6.50  --clausifier                            res/vclausify_rel
% 47.87/6.50  --clausifier_options                    --mode clausify
% 47.87/6.50  --stdin                                 false
% 47.87/6.50  --stats_out                             sel
% 47.87/6.50  
% 47.87/6.50  ------ General Options
% 47.87/6.50  
% 47.87/6.50  --fof                                   false
% 47.87/6.50  --time_out_real                         604.99
% 47.87/6.50  --time_out_virtual                      -1.
% 47.87/6.50  --symbol_type_check                     false
% 47.87/6.50  --clausify_out                          false
% 47.87/6.50  --sig_cnt_out                           false
% 47.87/6.50  --trig_cnt_out                          false
% 47.87/6.50  --trig_cnt_out_tolerance                1.
% 47.87/6.50  --trig_cnt_out_sk_spl                   false
% 47.87/6.50  --abstr_cl_out                          false
% 47.87/6.50  
% 47.87/6.50  ------ Global Options
% 47.87/6.50  
% 47.87/6.50  --schedule                              none
% 47.87/6.50  --add_important_lit                     false
% 47.87/6.50  --prop_solver_per_cl                    1000
% 47.87/6.50  --min_unsat_core                        false
% 47.87/6.50  --soft_assumptions                      false
% 47.87/6.50  --soft_lemma_size                       3
% 47.87/6.50  --prop_impl_unit_size                   0
% 47.87/6.50  --prop_impl_unit                        []
% 47.87/6.50  --share_sel_clauses                     true
% 47.87/6.50  --reset_solvers                         false
% 47.87/6.50  --bc_imp_inh                            [conj_cone]
% 47.87/6.50  --conj_cone_tolerance                   3.
% 47.87/6.50  --extra_neg_conj                        none
% 47.87/6.50  --large_theory_mode                     true
% 47.87/6.50  --prolific_symb_bound                   200
% 47.87/6.50  --lt_threshold                          2000
% 47.87/6.50  --clause_weak_htbl                      true
% 47.87/6.50  --gc_record_bc_elim                     false
% 47.87/6.50  
% 47.87/6.50  ------ Preprocessing Options
% 47.87/6.50  
% 47.87/6.50  --preprocessing_flag                    true
% 47.87/6.50  --time_out_prep_mult                    0.1
% 47.87/6.50  --splitting_mode                        input
% 47.87/6.50  --splitting_grd                         true
% 47.87/6.50  --splitting_cvd                         false
% 47.87/6.50  --splitting_cvd_svl                     false
% 47.87/6.50  --splitting_nvd                         32
% 47.87/6.50  --sub_typing                            true
% 47.87/6.50  --prep_gs_sim                           false
% 47.87/6.50  --prep_unflatten                        true
% 47.87/6.50  --prep_res_sim                          true
% 47.87/6.50  --prep_upred                            true
% 47.87/6.50  --prep_sem_filter                       exhaustive
% 47.87/6.50  --prep_sem_filter_out                   false
% 47.87/6.50  --pred_elim                             false
% 47.87/6.50  --res_sim_input                         true
% 47.87/6.50  --eq_ax_congr_red                       true
% 47.87/6.50  --pure_diseq_elim                       true
% 47.87/6.50  --brand_transform                       false
% 47.87/6.50  --non_eq_to_eq                          false
% 47.87/6.50  --prep_def_merge                        true
% 47.87/6.50  --prep_def_merge_prop_impl              false
% 47.87/6.50  --prep_def_merge_mbd                    true
% 47.87/6.50  --prep_def_merge_tr_red                 false
% 47.87/6.50  --prep_def_merge_tr_cl                  false
% 47.87/6.50  --smt_preprocessing                     true
% 47.87/6.50  --smt_ac_axioms                         fast
% 47.87/6.50  --preprocessed_out                      false
% 47.87/6.50  --preprocessed_stats                    false
% 47.87/6.50  
% 47.87/6.50  ------ Abstraction refinement Options
% 47.87/6.50  
% 47.87/6.50  --abstr_ref                             []
% 47.87/6.50  --abstr_ref_prep                        false
% 47.87/6.50  --abstr_ref_until_sat                   false
% 47.87/6.50  --abstr_ref_sig_restrict                funpre
% 47.87/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.87/6.50  --abstr_ref_under                       []
% 47.87/6.50  
% 47.87/6.50  ------ SAT Options
% 47.87/6.50  
% 47.87/6.50  --sat_mode                              false
% 47.87/6.50  --sat_fm_restart_options                ""
% 47.87/6.50  --sat_gr_def                            false
% 47.87/6.50  --sat_epr_types                         true
% 47.87/6.50  --sat_non_cyclic_types                  false
% 47.87/6.50  --sat_finite_models                     false
% 47.87/6.50  --sat_fm_lemmas                         false
% 47.87/6.50  --sat_fm_prep                           false
% 47.87/6.50  --sat_fm_uc_incr                        true
% 47.87/6.50  --sat_out_model                         small
% 47.87/6.50  --sat_out_clauses                       false
% 47.87/6.50  
% 47.87/6.50  ------ QBF Options
% 47.87/6.50  
% 47.87/6.50  --qbf_mode                              false
% 47.87/6.50  --qbf_elim_univ                         false
% 47.87/6.50  --qbf_dom_inst                          none
% 47.87/6.50  --qbf_dom_pre_inst                      false
% 47.87/6.50  --qbf_sk_in                             false
% 47.87/6.50  --qbf_pred_elim                         true
% 47.87/6.50  --qbf_split                             512
% 47.87/6.50  
% 47.87/6.50  ------ BMC1 Options
% 47.87/6.50  
% 47.87/6.50  --bmc1_incremental                      false
% 47.87/6.50  --bmc1_axioms                           reachable_all
% 47.87/6.50  --bmc1_min_bound                        0
% 47.87/6.50  --bmc1_max_bound                        -1
% 47.87/6.50  --bmc1_max_bound_default                -1
% 47.87/6.50  --bmc1_symbol_reachability              true
% 47.87/6.50  --bmc1_property_lemmas                  false
% 47.87/6.50  --bmc1_k_induction                      false
% 47.87/6.50  --bmc1_non_equiv_states                 false
% 47.87/6.50  --bmc1_deadlock                         false
% 47.87/6.50  --bmc1_ucm                              false
% 47.87/6.50  --bmc1_add_unsat_core                   none
% 47.87/6.50  --bmc1_unsat_core_children              false
% 47.87/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.87/6.50  --bmc1_out_stat                         full
% 47.87/6.50  --bmc1_ground_init                      false
% 47.87/6.50  --bmc1_pre_inst_next_state              false
% 47.87/6.50  --bmc1_pre_inst_state                   false
% 47.87/6.50  --bmc1_pre_inst_reach_state             false
% 47.87/6.50  --bmc1_out_unsat_core                   false
% 47.87/6.50  --bmc1_aig_witness_out                  false
% 47.87/6.50  --bmc1_verbose                          false
% 47.87/6.50  --bmc1_dump_clauses_tptp                false
% 47.87/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.87/6.50  --bmc1_dump_file                        -
% 47.87/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.87/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.87/6.50  --bmc1_ucm_extend_mode                  1
% 47.87/6.50  --bmc1_ucm_init_mode                    2
% 47.87/6.50  --bmc1_ucm_cone_mode                    none
% 47.87/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.87/6.50  --bmc1_ucm_relax_model                  4
% 47.87/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.87/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.87/6.50  --bmc1_ucm_layered_model                none
% 47.87/6.50  --bmc1_ucm_max_lemma_size               10
% 47.87/6.50  
% 47.87/6.50  ------ AIG Options
% 47.87/6.50  
% 47.87/6.50  --aig_mode                              false
% 47.87/6.50  
% 47.87/6.50  ------ Instantiation Options
% 47.87/6.50  
% 47.87/6.50  --instantiation_flag                    true
% 47.87/6.50  --inst_sos_flag                         false
% 47.87/6.50  --inst_sos_phase                        true
% 47.87/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.87/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.87/6.50  --inst_lit_sel_side                     num_symb
% 47.87/6.50  --inst_solver_per_active                1400
% 47.87/6.50  --inst_solver_calls_frac                1.
% 47.87/6.50  --inst_passive_queue_type               priority_queues
% 47.87/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.87/6.50  --inst_passive_queues_freq              [25;2]
% 47.87/6.50  --inst_dismatching                      true
% 47.87/6.50  --inst_eager_unprocessed_to_passive     true
% 47.87/6.50  --inst_prop_sim_given                   true
% 47.87/6.50  --inst_prop_sim_new                     false
% 47.87/6.50  --inst_subs_new                         false
% 47.87/6.50  --inst_eq_res_simp                      false
% 47.87/6.50  --inst_subs_given                       false
% 47.87/6.50  --inst_orphan_elimination               true
% 47.87/6.50  --inst_learning_loop_flag               true
% 47.87/6.50  --inst_learning_start                   3000
% 47.87/6.50  --inst_learning_factor                  2
% 47.87/6.50  --inst_start_prop_sim_after_learn       3
% 47.87/6.50  --inst_sel_renew                        solver
% 47.87/6.50  --inst_lit_activity_flag                true
% 47.87/6.50  --inst_restr_to_given                   false
% 47.87/6.50  --inst_activity_threshold               500
% 47.87/6.50  --inst_out_proof                        true
% 47.87/6.50  
% 47.87/6.50  ------ Resolution Options
% 47.87/6.50  
% 47.87/6.50  --resolution_flag                       true
% 47.87/6.50  --res_lit_sel                           adaptive
% 47.87/6.50  --res_lit_sel_side                      none
% 47.87/6.50  --res_ordering                          kbo
% 47.87/6.50  --res_to_prop_solver                    active
% 47.87/6.50  --res_prop_simpl_new                    false
% 47.87/6.50  --res_prop_simpl_given                  true
% 47.87/6.50  --res_passive_queue_type                priority_queues
% 47.87/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.87/6.50  --res_passive_queues_freq               [15;5]
% 47.87/6.50  --res_forward_subs                      full
% 47.87/6.50  --res_backward_subs                     full
% 47.87/6.50  --res_forward_subs_resolution           true
% 47.87/6.50  --res_backward_subs_resolution          true
% 47.87/6.50  --res_orphan_elimination                true
% 47.87/6.50  --res_time_limit                        2.
% 47.87/6.50  --res_out_proof                         true
% 47.87/6.50  
% 47.87/6.50  ------ Superposition Options
% 47.87/6.50  
% 47.87/6.50  --superposition_flag                    true
% 47.87/6.50  --sup_passive_queue_type                priority_queues
% 47.87/6.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.87/6.50  --sup_passive_queues_freq               [1;4]
% 47.87/6.50  --demod_completeness_check              fast
% 47.87/6.50  --demod_use_ground                      true
% 47.87/6.50  --sup_to_prop_solver                    passive
% 47.87/6.50  --sup_prop_simpl_new                    true
% 47.87/6.50  --sup_prop_simpl_given                  true
% 47.87/6.50  --sup_fun_splitting                     false
% 47.87/6.50  --sup_smt_interval                      50000
% 47.87/6.50  
% 47.87/6.50  ------ Superposition Simplification Setup
% 47.87/6.50  
% 47.87/6.50  --sup_indices_passive                   []
% 47.87/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.87/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_full_bw                           [BwDemod]
% 47.87/6.50  --sup_immed_triv                        [TrivRules]
% 47.87/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.87/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_immed_bw_main                     []
% 47.87/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.87/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.87/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.87/6.50  
% 47.87/6.50  ------ Combination Options
% 47.87/6.50  
% 47.87/6.50  --comb_res_mult                         3
% 47.87/6.50  --comb_sup_mult                         2
% 47.87/6.50  --comb_inst_mult                        10
% 47.87/6.50  
% 47.87/6.50  ------ Debug Options
% 47.87/6.50  
% 47.87/6.50  --dbg_backtrace                         false
% 47.87/6.50  --dbg_dump_prop_clauses                 false
% 47.87/6.50  --dbg_dump_prop_clauses_file            -
% 47.87/6.50  --dbg_out_stat                          false
% 47.87/6.50  ------ Parsing...
% 47.87/6.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.87/6.50  
% 47.87/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 47.87/6.50  
% 47.87/6.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.87/6.50  
% 47.87/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.87/6.50  ------ Proving...
% 47.87/6.50  ------ Problem Properties 
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  clauses                                 38
% 47.87/6.50  conjectures                             9
% 47.87/6.50  EPR                                     9
% 47.87/6.50  Horn                                    33
% 47.87/6.50  unary                                   12
% 47.87/6.50  binary                                  11
% 47.87/6.50  lits                                    89
% 47.87/6.50  lits eq                                 11
% 47.87/6.50  fd_pure                                 0
% 47.87/6.50  fd_pseudo                               0
% 47.87/6.50  fd_cond                                 1
% 47.87/6.50  fd_pseudo_cond                          0
% 47.87/6.50  AC symbols                              0
% 47.87/6.50  
% 47.87/6.50  ------ Input Options Time Limit: Unbounded
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  ------ 
% 47.87/6.50  Current options:
% 47.87/6.50  ------ 
% 47.87/6.50  
% 47.87/6.50  ------ Input Options
% 47.87/6.50  
% 47.87/6.50  --out_options                           all
% 47.87/6.50  --tptp_safe_out                         true
% 47.87/6.50  --problem_path                          ""
% 47.87/6.50  --include_path                          ""
% 47.87/6.50  --clausifier                            res/vclausify_rel
% 47.87/6.50  --clausifier_options                    --mode clausify
% 47.87/6.50  --stdin                                 false
% 47.87/6.50  --stats_out                             sel
% 47.87/6.50  
% 47.87/6.50  ------ General Options
% 47.87/6.50  
% 47.87/6.50  --fof                                   false
% 47.87/6.50  --time_out_real                         604.99
% 47.87/6.50  --time_out_virtual                      -1.
% 47.87/6.50  --symbol_type_check                     false
% 47.87/6.50  --clausify_out                          false
% 47.87/6.50  --sig_cnt_out                           false
% 47.87/6.50  --trig_cnt_out                          false
% 47.87/6.50  --trig_cnt_out_tolerance                1.
% 47.87/6.50  --trig_cnt_out_sk_spl                   false
% 47.87/6.50  --abstr_cl_out                          false
% 47.87/6.50  
% 47.87/6.50  ------ Global Options
% 47.87/6.50  
% 47.87/6.50  --schedule                              none
% 47.87/6.50  --add_important_lit                     false
% 47.87/6.50  --prop_solver_per_cl                    1000
% 47.87/6.50  --min_unsat_core                        false
% 47.87/6.50  --soft_assumptions                      false
% 47.87/6.50  --soft_lemma_size                       3
% 47.87/6.50  --prop_impl_unit_size                   0
% 47.87/6.50  --prop_impl_unit                        []
% 47.87/6.50  --share_sel_clauses                     true
% 47.87/6.50  --reset_solvers                         false
% 47.87/6.50  --bc_imp_inh                            [conj_cone]
% 47.87/6.50  --conj_cone_tolerance                   3.
% 47.87/6.50  --extra_neg_conj                        none
% 47.87/6.50  --large_theory_mode                     true
% 47.87/6.50  --prolific_symb_bound                   200
% 47.87/6.50  --lt_threshold                          2000
% 47.87/6.50  --clause_weak_htbl                      true
% 47.87/6.50  --gc_record_bc_elim                     false
% 47.87/6.50  
% 47.87/6.50  ------ Preprocessing Options
% 47.87/6.50  
% 47.87/6.50  --preprocessing_flag                    true
% 47.87/6.50  --time_out_prep_mult                    0.1
% 47.87/6.50  --splitting_mode                        input
% 47.87/6.50  --splitting_grd                         true
% 47.87/6.50  --splitting_cvd                         false
% 47.87/6.50  --splitting_cvd_svl                     false
% 47.87/6.50  --splitting_nvd                         32
% 47.87/6.50  --sub_typing                            true
% 47.87/6.50  --prep_gs_sim                           false
% 47.87/6.50  --prep_unflatten                        true
% 47.87/6.50  --prep_res_sim                          true
% 47.87/6.50  --prep_upred                            true
% 47.87/6.50  --prep_sem_filter                       exhaustive
% 47.87/6.50  --prep_sem_filter_out                   false
% 47.87/6.50  --pred_elim                             false
% 47.87/6.50  --res_sim_input                         true
% 47.87/6.50  --eq_ax_congr_red                       true
% 47.87/6.50  --pure_diseq_elim                       true
% 47.87/6.50  --brand_transform                       false
% 47.87/6.50  --non_eq_to_eq                          false
% 47.87/6.50  --prep_def_merge                        true
% 47.87/6.50  --prep_def_merge_prop_impl              false
% 47.87/6.50  --prep_def_merge_mbd                    true
% 47.87/6.50  --prep_def_merge_tr_red                 false
% 47.87/6.50  --prep_def_merge_tr_cl                  false
% 47.87/6.50  --smt_preprocessing                     true
% 47.87/6.50  --smt_ac_axioms                         fast
% 47.87/6.50  --preprocessed_out                      false
% 47.87/6.50  --preprocessed_stats                    false
% 47.87/6.50  
% 47.87/6.50  ------ Abstraction refinement Options
% 47.87/6.50  
% 47.87/6.50  --abstr_ref                             []
% 47.87/6.50  --abstr_ref_prep                        false
% 47.87/6.50  --abstr_ref_until_sat                   false
% 47.87/6.50  --abstr_ref_sig_restrict                funpre
% 47.87/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.87/6.50  --abstr_ref_under                       []
% 47.87/6.50  
% 47.87/6.50  ------ SAT Options
% 47.87/6.50  
% 47.87/6.50  --sat_mode                              false
% 47.87/6.50  --sat_fm_restart_options                ""
% 47.87/6.50  --sat_gr_def                            false
% 47.87/6.50  --sat_epr_types                         true
% 47.87/6.50  --sat_non_cyclic_types                  false
% 47.87/6.50  --sat_finite_models                     false
% 47.87/6.50  --sat_fm_lemmas                         false
% 47.87/6.50  --sat_fm_prep                           false
% 47.87/6.50  --sat_fm_uc_incr                        true
% 47.87/6.50  --sat_out_model                         small
% 47.87/6.50  --sat_out_clauses                       false
% 47.87/6.50  
% 47.87/6.50  ------ QBF Options
% 47.87/6.50  
% 47.87/6.50  --qbf_mode                              false
% 47.87/6.50  --qbf_elim_univ                         false
% 47.87/6.50  --qbf_dom_inst                          none
% 47.87/6.50  --qbf_dom_pre_inst                      false
% 47.87/6.50  --qbf_sk_in                             false
% 47.87/6.50  --qbf_pred_elim                         true
% 47.87/6.50  --qbf_split                             512
% 47.87/6.50  
% 47.87/6.50  ------ BMC1 Options
% 47.87/6.50  
% 47.87/6.50  --bmc1_incremental                      false
% 47.87/6.50  --bmc1_axioms                           reachable_all
% 47.87/6.50  --bmc1_min_bound                        0
% 47.87/6.50  --bmc1_max_bound                        -1
% 47.87/6.50  --bmc1_max_bound_default                -1
% 47.87/6.50  --bmc1_symbol_reachability              true
% 47.87/6.50  --bmc1_property_lemmas                  false
% 47.87/6.50  --bmc1_k_induction                      false
% 47.87/6.50  --bmc1_non_equiv_states                 false
% 47.87/6.50  --bmc1_deadlock                         false
% 47.87/6.50  --bmc1_ucm                              false
% 47.87/6.50  --bmc1_add_unsat_core                   none
% 47.87/6.50  --bmc1_unsat_core_children              false
% 47.87/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.87/6.50  --bmc1_out_stat                         full
% 47.87/6.50  --bmc1_ground_init                      false
% 47.87/6.50  --bmc1_pre_inst_next_state              false
% 47.87/6.50  --bmc1_pre_inst_state                   false
% 47.87/6.50  --bmc1_pre_inst_reach_state             false
% 47.87/6.50  --bmc1_out_unsat_core                   false
% 47.87/6.50  --bmc1_aig_witness_out                  false
% 47.87/6.50  --bmc1_verbose                          false
% 47.87/6.50  --bmc1_dump_clauses_tptp                false
% 47.87/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.87/6.50  --bmc1_dump_file                        -
% 47.87/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.87/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.87/6.50  --bmc1_ucm_extend_mode                  1
% 47.87/6.50  --bmc1_ucm_init_mode                    2
% 47.87/6.50  --bmc1_ucm_cone_mode                    none
% 47.87/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.87/6.50  --bmc1_ucm_relax_model                  4
% 47.87/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.87/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.87/6.50  --bmc1_ucm_layered_model                none
% 47.87/6.50  --bmc1_ucm_max_lemma_size               10
% 47.87/6.50  
% 47.87/6.50  ------ AIG Options
% 47.87/6.50  
% 47.87/6.50  --aig_mode                              false
% 47.87/6.50  
% 47.87/6.50  ------ Instantiation Options
% 47.87/6.50  
% 47.87/6.50  --instantiation_flag                    true
% 47.87/6.50  --inst_sos_flag                         false
% 47.87/6.50  --inst_sos_phase                        true
% 47.87/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.87/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.87/6.50  --inst_lit_sel_side                     num_symb
% 47.87/6.50  --inst_solver_per_active                1400
% 47.87/6.50  --inst_solver_calls_frac                1.
% 47.87/6.50  --inst_passive_queue_type               priority_queues
% 47.87/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.87/6.50  --inst_passive_queues_freq              [25;2]
% 47.87/6.50  --inst_dismatching                      true
% 47.87/6.50  --inst_eager_unprocessed_to_passive     true
% 47.87/6.50  --inst_prop_sim_given                   true
% 47.87/6.50  --inst_prop_sim_new                     false
% 47.87/6.50  --inst_subs_new                         false
% 47.87/6.50  --inst_eq_res_simp                      false
% 47.87/6.50  --inst_subs_given                       false
% 47.87/6.50  --inst_orphan_elimination               true
% 47.87/6.50  --inst_learning_loop_flag               true
% 47.87/6.50  --inst_learning_start                   3000
% 47.87/6.50  --inst_learning_factor                  2
% 47.87/6.50  --inst_start_prop_sim_after_learn       3
% 47.87/6.50  --inst_sel_renew                        solver
% 47.87/6.50  --inst_lit_activity_flag                true
% 47.87/6.50  --inst_restr_to_given                   false
% 47.87/6.50  --inst_activity_threshold               500
% 47.87/6.50  --inst_out_proof                        true
% 47.87/6.50  
% 47.87/6.50  ------ Resolution Options
% 47.87/6.50  
% 47.87/6.50  --resolution_flag                       true
% 47.87/6.50  --res_lit_sel                           adaptive
% 47.87/6.50  --res_lit_sel_side                      none
% 47.87/6.50  --res_ordering                          kbo
% 47.87/6.50  --res_to_prop_solver                    active
% 47.87/6.50  --res_prop_simpl_new                    false
% 47.87/6.50  --res_prop_simpl_given                  true
% 47.87/6.50  --res_passive_queue_type                priority_queues
% 47.87/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.87/6.50  --res_passive_queues_freq               [15;5]
% 47.87/6.50  --res_forward_subs                      full
% 47.87/6.50  --res_backward_subs                     full
% 47.87/6.50  --res_forward_subs_resolution           true
% 47.87/6.50  --res_backward_subs_resolution          true
% 47.87/6.50  --res_orphan_elimination                true
% 47.87/6.50  --res_time_limit                        2.
% 47.87/6.50  --res_out_proof                         true
% 47.87/6.50  
% 47.87/6.50  ------ Superposition Options
% 47.87/6.50  
% 47.87/6.50  --superposition_flag                    true
% 47.87/6.50  --sup_passive_queue_type                priority_queues
% 47.87/6.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.87/6.50  --sup_passive_queues_freq               [1;4]
% 47.87/6.50  --demod_completeness_check              fast
% 47.87/6.50  --demod_use_ground                      true
% 47.87/6.50  --sup_to_prop_solver                    passive
% 47.87/6.50  --sup_prop_simpl_new                    true
% 47.87/6.50  --sup_prop_simpl_given                  true
% 47.87/6.50  --sup_fun_splitting                     false
% 47.87/6.50  --sup_smt_interval                      50000
% 47.87/6.50  
% 47.87/6.50  ------ Superposition Simplification Setup
% 47.87/6.50  
% 47.87/6.50  --sup_indices_passive                   []
% 47.87/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.87/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.87/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_full_bw                           [BwDemod]
% 47.87/6.50  --sup_immed_triv                        [TrivRules]
% 47.87/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.87/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_immed_bw_main                     []
% 47.87/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.87/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.87/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.87/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.87/6.50  
% 47.87/6.50  ------ Combination Options
% 47.87/6.50  
% 47.87/6.50  --comb_res_mult                         3
% 47.87/6.50  --comb_sup_mult                         2
% 47.87/6.50  --comb_inst_mult                        10
% 47.87/6.50  
% 47.87/6.50  ------ Debug Options
% 47.87/6.50  
% 47.87/6.50  --dbg_backtrace                         false
% 47.87/6.50  --dbg_dump_prop_clauses                 false
% 47.87/6.50  --dbg_dump_prop_clauses_file            -
% 47.87/6.50  --dbg_out_stat                          false
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  ------ Proving...
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  % SZS status Theorem for theBenchmark.p
% 47.87/6.50  
% 47.87/6.50  % SZS output start CNFRefutation for theBenchmark.p
% 47.87/6.50  
% 47.87/6.50  fof(f24,conjecture,(
% 47.87/6.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f25,negated_conjecture,(
% 47.87/6.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 47.87/6.50    inference(negated_conjecture,[],[f24])).
% 47.87/6.50  
% 47.87/6.50  fof(f53,plain,(
% 47.87/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 47.87/6.50    inference(ennf_transformation,[],[f25])).
% 47.87/6.50  
% 47.87/6.50  fof(f54,plain,(
% 47.87/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 47.87/6.50    inference(flattening,[],[f53])).
% 47.87/6.50  
% 47.87/6.50  fof(f61,plain,(
% 47.87/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 47.87/6.50    inference(nnf_transformation,[],[f54])).
% 47.87/6.50  
% 47.87/6.50  fof(f62,plain,(
% 47.87/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 47.87/6.50    inference(flattening,[],[f61])).
% 47.87/6.50  
% 47.87/6.50  fof(f67,plain,(
% 47.87/6.50    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f66,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & (r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f65,plain,(
% 47.87/6.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f64,plain,(
% 47.87/6.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f63,plain,(
% 47.87/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f68,plain,(
% 47.87/6.50    (((((~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & (r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 47.87/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f62,f67,f66,f65,f64,f63])).
% 47.87/6.50  
% 47.87/6.50  fof(f105,plain,(
% 47.87/6.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f20,axiom,(
% 47.87/6.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f46,plain,(
% 47.87/6.50    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.87/6.50    inference(ennf_transformation,[],[f20])).
% 47.87/6.50  
% 47.87/6.50  fof(f92,plain,(
% 47.87/6.50    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.87/6.50    inference(cnf_transformation,[],[f46])).
% 47.87/6.50  
% 47.87/6.50  fof(f22,axiom,(
% 47.87/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f49,plain,(
% 47.87/6.50    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 47.87/6.50    inference(ennf_transformation,[],[f22])).
% 47.87/6.50  
% 47.87/6.50  fof(f50,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 47.87/6.50    inference(flattening,[],[f49])).
% 47.87/6.50  
% 47.87/6.50  fof(f96,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f50])).
% 47.87/6.50  
% 47.87/6.50  fof(f102,plain,(
% 47.87/6.50    ~v1_xboole_0(sK2)),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f103,plain,(
% 47.87/6.50    v1_funct_1(sK3)),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f104,plain,(
% 47.87/6.50    v1_funct_2(sK3,sK1,sK2)),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f6,axiom,(
% 47.87/6.50    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f57,plain,(
% 47.87/6.50    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 47.87/6.50    introduced(choice_axiom,[])).
% 47.87/6.50  
% 47.87/6.50  fof(f58,plain,(
% 47.87/6.50    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 47.87/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f57])).
% 47.87/6.50  
% 47.87/6.50  fof(f76,plain,(
% 47.87/6.50    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f58])).
% 47.87/6.50  
% 47.87/6.50  fof(f8,axiom,(
% 47.87/6.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f32,plain,(
% 47.87/6.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 47.87/6.50    inference(ennf_transformation,[],[f8])).
% 47.87/6.50  
% 47.87/6.50  fof(f33,plain,(
% 47.87/6.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 47.87/6.50    inference(flattening,[],[f32])).
% 47.87/6.50  
% 47.87/6.50  fof(f78,plain,(
% 47.87/6.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f33])).
% 47.87/6.50  
% 47.87/6.50  fof(f4,axiom,(
% 47.87/6.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f72,plain,(
% 47.87/6.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f4])).
% 47.87/6.50  
% 47.87/6.50  fof(f17,axiom,(
% 47.87/6.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f43,plain,(
% 47.87/6.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 47.87/6.50    inference(ennf_transformation,[],[f17])).
% 47.87/6.50  
% 47.87/6.50  fof(f89,plain,(
% 47.87/6.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f43])).
% 47.87/6.50  
% 47.87/6.50  fof(f14,axiom,(
% 47.87/6.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f38,plain,(
% 47.87/6.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 47.87/6.50    inference(ennf_transformation,[],[f14])).
% 47.87/6.50  
% 47.87/6.50  fof(f86,plain,(
% 47.87/6.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f38])).
% 47.87/6.50  
% 47.87/6.50  fof(f108,plain,(
% 47.87/6.50    r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f19,axiom,(
% 47.87/6.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f45,plain,(
% 47.87/6.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.87/6.50    inference(ennf_transformation,[],[f19])).
% 47.87/6.50  
% 47.87/6.50  fof(f91,plain,(
% 47.87/6.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.87/6.50    inference(cnf_transformation,[],[f45])).
% 47.87/6.50  
% 47.87/6.50  fof(f2,axiom,(
% 47.87/6.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f28,plain,(
% 47.87/6.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 47.87/6.50    inference(ennf_transformation,[],[f2])).
% 47.87/6.50  
% 47.87/6.50  fof(f70,plain,(
% 47.87/6.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f28])).
% 47.87/6.50  
% 47.87/6.50  fof(f9,axiom,(
% 47.87/6.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f59,plain,(
% 47.87/6.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.87/6.50    inference(nnf_transformation,[],[f9])).
% 47.87/6.50  
% 47.87/6.50  fof(f79,plain,(
% 47.87/6.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.87/6.50    inference(cnf_transformation,[],[f59])).
% 47.87/6.50  
% 47.87/6.50  fof(f3,axiom,(
% 47.87/6.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f29,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 47.87/6.50    inference(ennf_transformation,[],[f3])).
% 47.87/6.50  
% 47.87/6.50  fof(f30,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 47.87/6.50    inference(flattening,[],[f29])).
% 47.87/6.50  
% 47.87/6.50  fof(f71,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f30])).
% 47.87/6.50  
% 47.87/6.50  fof(f10,axiom,(
% 47.87/6.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f34,plain,(
% 47.87/6.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 47.87/6.50    inference(ennf_transformation,[],[f10])).
% 47.87/6.50  
% 47.87/6.50  fof(f81,plain,(
% 47.87/6.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f34])).
% 47.87/6.50  
% 47.87/6.50  fof(f80,plain,(
% 47.87/6.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f59])).
% 47.87/6.50  
% 47.87/6.50  fof(f12,axiom,(
% 47.87/6.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f84,plain,(
% 47.87/6.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 47.87/6.50    inference(cnf_transformation,[],[f12])).
% 47.87/6.50  
% 47.87/6.50  fof(f16,axiom,(
% 47.87/6.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f41,plain,(
% 47.87/6.50    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 47.87/6.50    inference(ennf_transformation,[],[f16])).
% 47.87/6.50  
% 47.87/6.50  fof(f42,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 47.87/6.50    inference(flattening,[],[f41])).
% 47.87/6.50  
% 47.87/6.50  fof(f88,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f42])).
% 47.87/6.50  
% 47.87/6.50  fof(f109,plain,(
% 47.87/6.50    ~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  fof(f15,axiom,(
% 47.87/6.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f39,plain,(
% 47.87/6.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 47.87/6.50    inference(ennf_transformation,[],[f15])).
% 47.87/6.50  
% 47.87/6.50  fof(f40,plain,(
% 47.87/6.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.87/6.50    inference(flattening,[],[f39])).
% 47.87/6.50  
% 47.87/6.50  fof(f87,plain,(
% 47.87/6.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f40])).
% 47.87/6.50  
% 47.87/6.50  fof(f13,axiom,(
% 47.87/6.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f36,plain,(
% 47.87/6.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 47.87/6.50    inference(ennf_transformation,[],[f13])).
% 47.87/6.50  
% 47.87/6.50  fof(f37,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 47.87/6.50    inference(flattening,[],[f36])).
% 47.87/6.50  
% 47.87/6.50  fof(f85,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f37])).
% 47.87/6.50  
% 47.87/6.50  fof(f1,axiom,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 47.87/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.87/6.50  
% 47.87/6.50  fof(f27,plain,(
% 47.87/6.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 47.87/6.50    inference(ennf_transformation,[],[f1])).
% 47.87/6.50  
% 47.87/6.50  fof(f69,plain,(
% 47.87/6.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 47.87/6.50    inference(cnf_transformation,[],[f27])).
% 47.87/6.50  
% 47.87/6.50  fof(f106,plain,(
% 47.87/6.50    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 47.87/6.50    inference(cnf_transformation,[],[f68])).
% 47.87/6.50  
% 47.87/6.50  cnf(c_36,negated_conjecture,
% 47.87/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 47.87/6.50      inference(cnf_transformation,[],[f105]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1427,plain,
% 47.87/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_23,plain,
% 47.87/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.87/6.50      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 47.87/6.50      inference(cnf_transformation,[],[f92]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1437,plain,
% 47.87/6.50      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 47.87/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3091,plain,
% 47.87/6.50      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1427,c_1437]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_28,plain,
% 47.87/6.50      ( ~ v1_funct_2(X0,X1,X2)
% 47.87/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.87/6.50      | ~ v1_funct_1(X0)
% 47.87/6.50      | k8_relset_1(X1,X2,X0,X2) = X1
% 47.87/6.50      | k1_xboole_0 = X2 ),
% 47.87/6.50      inference(cnf_transformation,[],[f96]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1434,plain,
% 47.87/6.50      ( k8_relset_1(X0,X1,X2,X1) = X0
% 47.87/6.50      | k1_xboole_0 = X1
% 47.87/6.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.87/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.87/6.50      | v1_funct_1(X2) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3892,plain,
% 47.87/6.50      ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1
% 47.87/6.50      | sK2 = k1_xboole_0
% 47.87/6.50      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 47.87/6.50      | v1_funct_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1427,c_1434]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_39,negated_conjecture,
% 47.87/6.50      ( ~ v1_xboole_0(sK2) ),
% 47.87/6.50      inference(cnf_transformation,[],[f102]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_38,negated_conjecture,
% 47.87/6.50      ( v1_funct_1(sK3) ),
% 47.87/6.50      inference(cnf_transformation,[],[f103]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_37,negated_conjecture,
% 47.87/6.50      ( v1_funct_2(sK3,sK1,sK2) ),
% 47.87/6.50      inference(cnf_transformation,[],[f104]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_654,plain,
% 47.87/6.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 47.87/6.50      theory(equality) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2083,plain,
% 47.87/6.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_654]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2085,plain,
% 47.87/6.50      ( v1_xboole_0(sK2)
% 47.87/6.50      | ~ v1_xboole_0(k1_xboole_0)
% 47.87/6.50      | sK2 != k1_xboole_0 ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_2083]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_7,plain,
% 47.87/6.50      ( m1_subset_1(sK0(X0),X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f76]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1452,plain,
% 47.87/6.50      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_9,plain,
% 47.87/6.50      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 47.87/6.50      inference(cnf_transformation,[],[f78]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1450,plain,
% 47.87/6.50      ( r2_hidden(X0,X1) = iProver_top
% 47.87/6.50      | m1_subset_1(X0,X1) != iProver_top
% 47.87/6.50      | v1_xboole_0(X1) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3050,plain,
% 47.87/6.50      ( r2_hidden(sK0(X0),X0) = iProver_top
% 47.87/6.50      | v1_xboole_0(X0) = iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1452,c_1450]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3077,plain,
% 47.87/6.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 47.87/6.50      inference(predicate_to_equality_rev,[status(thm)],[c_3050]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3079,plain,
% 47.87/6.50      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 47.87/6.50      | v1_xboole_0(k1_xboole_0) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_3077]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3946,plain,
% 47.87/6.50      ( ~ v1_funct_2(sK3,sK1,sK2)
% 47.87/6.50      | ~ v1_funct_1(sK3)
% 47.87/6.50      | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
% 47.87/6.50      | sK2 = k1_xboole_0 ),
% 47.87/6.50      inference(predicate_to_equality_rev,[status(thm)],[c_3892]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3,plain,
% 47.87/6.50      ( r1_tarski(k1_xboole_0,X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f72]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_4495,plain,
% 47.87/6.50      ( r1_tarski(k1_xboole_0,sK0(X0)) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_3]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_4499,plain,
% 47.87/6.50      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_4495]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_20,plain,
% 47.87/6.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f89]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_6735,plain,
% 47.87/6.50      ( ~ r2_hidden(sK0(X0),X0) | ~ r1_tarski(X0,sK0(X0)) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_20]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_6737,plain,
% 47.87/6.50      ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 47.87/6.50      | ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_6735]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_16566,plain,
% 47.87/6.50      ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1 ),
% 47.87/6.50      inference(global_propositional_subsumption,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_3892,c_39,c_38,c_37,c_2085,c_3079,c_3946,c_4499,
% 47.87/6.50                 c_6737]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_16569,plain,
% 47.87/6.50      ( k10_relat_1(sK3,sK2) = sK1 ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_3091,c_16566]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_17,plain,
% 47.87/6.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f86]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1443,plain,
% 47.87/6.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 47.87/6.50      | v1_relat_1(X0) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_200284,plain,
% 47.87/6.50      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 47.87/6.50      | v1_relat_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_16569,c_1443]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_33,negated_conjecture,
% 47.87/6.50      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 47.87/6.50      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 47.87/6.50      inference(cnf_transformation,[],[f108]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1430,plain,
% 47.87/6.50      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_6880,plain,
% 47.87/6.50      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 47.87/6.50      inference(demodulation,[status(thm)],[c_3091,c_1430]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_22,plain,
% 47.87/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.87/6.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 47.87/6.50      inference(cnf_transformation,[],[f91]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1438,plain,
% 47.87/6.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 47.87/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_3548,plain,
% 47.87/6.50      ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1427,c_1438]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_13366,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 47.87/6.50      inference(demodulation,[status(thm)],[c_6880,c_3548]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 47.87/6.50      inference(cnf_transformation,[],[f70]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1455,plain,
% 47.87/6.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_13372,plain,
% 47.87/6.50      ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_13366,c_1455]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_11,plain,
% 47.87/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.87/6.50      inference(cnf_transformation,[],[f79]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1448,plain,
% 47.87/6.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.87/6.50      | r1_tarski(X0,X1) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2424,plain,
% 47.87/6.50      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1452,c_1448]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 47.87/6.50      inference(cnf_transformation,[],[f71]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1454,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) != iProver_top
% 47.87/6.50      | r1_tarski(X1,X2) != iProver_top
% 47.87/6.50      | r1_tarski(X0,X2) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_6303,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) != iProver_top
% 47.87/6.50      | r1_tarski(sK0(k1_zfmisc_1(X0)),X1) = iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_2424,c_1454]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_10150,plain,
% 47.87/6.50      ( k2_xboole_0(sK0(k1_zfmisc_1(X0)),X1) = X1
% 47.87/6.50      | r1_tarski(X0,X1) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_6303,c_1455]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_13413,plain,
% 47.87/6.50      ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
% 47.87/6.50      | k2_xboole_0(sK0(k1_zfmisc_1(sK4)),k10_relat_1(sK3,sK5)) = k10_relat_1(sK3,sK5) ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_13372,c_10150]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_43,plain,
% 47.87/6.50      ( v1_funct_1(sK3) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_12,plain,
% 47.87/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.87/6.50      | ~ v1_relat_1(X1)
% 47.87/6.50      | v1_relat_1(X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f81]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_10,plain,
% 47.87/6.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.87/6.50      inference(cnf_transformation,[],[f80]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_247,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.87/6.50      inference(prop_impl,[status(thm)],[c_10]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_248,plain,
% 47.87/6.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.87/6.50      inference(renaming,[status(thm)],[c_247]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_319,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 47.87/6.50      inference(bin_hyper_res,[status(thm)],[c_12,c_248]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1959,plain,
% 47.87/6.50      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
% 47.87/6.50      inference(resolution,[status(thm)],[c_11,c_36]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2224,plain,
% 47.87/6.50      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) ),
% 47.87/6.50      inference(resolution,[status(thm)],[c_319,c_1959]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_15,plain,
% 47.87/6.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 47.87/6.50      inference(cnf_transformation,[],[f84]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2448,plain,
% 47.87/6.50      ( v1_relat_1(sK3) ),
% 47.87/6.50      inference(forward_subsumption_resolution,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_2224,c_15]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2449,plain,
% 47.87/6.50      ( v1_relat_1(sK3) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_13414,plain,
% 47.87/6.50      ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
% 47.87/6.50      | r1_tarski(k10_relat_1(sK3,sK5),X0) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,X0) = iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_13372,c_1454]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_23330,plain,
% 47.87/6.50      ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) = iProver_top
% 47.87/6.50      | v1_relat_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1443,c_13414]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_19,plain,
% 47.87/6.50      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 47.87/6.50      | ~ r1_tarski(X0,k1_relat_1(X1))
% 47.87/6.50      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 47.87/6.50      | ~ v1_funct_1(X1)
% 47.87/6.50      | ~ v1_relat_1(X1) ),
% 47.87/6.50      inference(cnf_transformation,[],[f88]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1441,plain,
% 47.87/6.50      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 47.87/6.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 47.87/6.50      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 47.87/6.50      | v1_funct_1(X1) != iProver_top
% 47.87/6.50      | v1_relat_1(X1) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_13374,plain,
% 47.87/6.50      ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
% 47.87/6.50      | v1_funct_1(sK3) != iProver_top
% 47.87/6.50      | v1_relat_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_13366,c_1441]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_39155,plain,
% 47.87/6.50      ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 47.87/6.50      inference(global_propositional_subsumption,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_13374,c_43,c_2449]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_32,negated_conjecture,
% 47.87/6.50      ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 47.87/6.50      | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 47.87/6.50      inference(cnf_transformation,[],[f109]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1431,plain,
% 47.87/6.50      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_6879,plain,
% 47.87/6.50      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 47.87/6.50      inference(demodulation,[status(thm)],[c_3091,c_1431]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_15608,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 47.87/6.50      inference(demodulation,[status(thm)],[c_6879,c_3548]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_39170,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_39155,c_15608]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_18,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 47.87/6.50      | ~ v1_funct_1(X0)
% 47.87/6.50      | ~ v1_relat_1(X0) ),
% 47.87/6.50      inference(cnf_transformation,[],[f87]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1442,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 47.87/6.50      | v1_funct_1(X0) != iProver_top
% 47.87/6.50      | v1_relat_1(X0) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_16,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1)
% 47.87/6.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 47.87/6.50      | ~ v1_relat_1(X2) ),
% 47.87/6.50      inference(cnf_transformation,[],[f85]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1444,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) != iProver_top
% 47.87/6.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 47.87/6.50      | v1_relat_1(X2) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_4802,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) != iProver_top
% 47.87/6.50      | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
% 47.87/6.50      | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
% 47.87/6.50      | v1_relat_1(X2) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1444,c_1454]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_27487,plain,
% 47.87/6.50      ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
% 47.87/6.50      | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
% 47.87/6.50      | v1_funct_1(X1) != iProver_top
% 47.87/6.50      | v1_relat_1(X1) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_1442,c_4802]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_59281,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
% 47.87/6.50      | v1_funct_1(sK3) != iProver_top
% 47.87/6.50      | v1_relat_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_39155,c_27487]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_126041,plain,
% 47.87/6.50      ( k2_xboole_0(k9_relat_1(sK3,sK4),sK5) = sK5 ),
% 47.87/6.50      inference(global_propositional_subsumption,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_13413,c_43,c_2449,c_23330,c_39170,c_59281]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_0,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 47.87/6.50      inference(cnf_transformation,[],[f69]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1456,plain,
% 47.87/6.50      ( r1_tarski(X0,X1) = iProver_top
% 47.87/6.50      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_126044,plain,
% 47.87/6.50      ( r1_tarski(k9_relat_1(sK3,sK4),X0) = iProver_top
% 47.87/6.50      | r1_tarski(sK5,X0) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_126041,c_1456]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_126294,plain,
% 47.87/6.50      ( r1_tarski(sK5,X0) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k10_relat_1(sK3,X0)) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top
% 47.87/6.50      | v1_funct_1(sK3) != iProver_top
% 47.87/6.50      | v1_relat_1(sK3) != iProver_top ),
% 47.87/6.50      inference(superposition,[status(thm)],[c_126044,c_1441]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_198496,plain,
% 47.87/6.50      ( r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 47.87/6.50      inference(global_propositional_subsumption,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_126294,c_43,c_2449,c_39170,c_59281]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2013,plain,
% 47.87/6.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_2]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_2653,plain,
% 47.87/6.50      ( ~ r1_tarski(sK1,X0) | r1_tarski(sK4,X0) | ~ r1_tarski(sK4,sK1) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_2013]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_12439,plain,
% 47.87/6.50      ( ~ r1_tarski(sK1,k1_relat_1(sK3))
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3))
% 47.87/6.50      | ~ r1_tarski(sK4,sK1) ),
% 47.87/6.50      inference(instantiation,[status(thm)],[c_2653]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_12444,plain,
% 47.87/6.50      ( r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
% 47.87/6.50      | r1_tarski(sK4,k1_relat_1(sK3)) = iProver_top
% 47.87/6.50      | r1_tarski(sK4,sK1) != iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_12439]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_35,negated_conjecture,
% 47.87/6.50      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 47.87/6.50      inference(cnf_transformation,[],[f106]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1957,plain,
% 47.87/6.50      ( r1_tarski(sK4,sK1) ),
% 47.87/6.50      inference(resolution,[status(thm)],[c_11,c_35]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(c_1958,plain,
% 47.87/6.50      ( r1_tarski(sK4,sK1) = iProver_top ),
% 47.87/6.50      inference(predicate_to_equality,[status(thm)],[c_1957]) ).
% 47.87/6.50  
% 47.87/6.50  cnf(contradiction,plain,
% 47.87/6.50      ( $false ),
% 47.87/6.50      inference(minisat,
% 47.87/6.50                [status(thm)],
% 47.87/6.50                [c_200284,c_198496,c_12444,c_2449,c_1958]) ).
% 47.87/6.50  
% 47.87/6.50  
% 47.87/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 47.87/6.50  
% 47.87/6.50  ------                               Statistics
% 47.87/6.50  
% 47.87/6.50  ------ Selected
% 47.87/6.50  
% 47.87/6.50  total_time:                             6.004
% 47.87/6.50  
%------------------------------------------------------------------------------
