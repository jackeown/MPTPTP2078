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
% DateTime   : Thu Dec  3 12:09:10 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 743 expanded)
%              Number of clauses        :   80 ( 212 expanded)
%              Number of leaves         :   19 ( 226 expanded)
%              Depth                    :   21
%              Number of atoms          :  512 (5555 expanded)
%              Number of equality atoms :  157 ( 357 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4))
          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4) )
        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4))
          | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4) )
        & m1_subset_1(sK4,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
            ( ( ~ r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4))
              | ~ r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4) )
            & ( r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4))
              | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4))
                  | ~ r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4))
                  | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(X1)) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2,X0,X1)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                    ( ( ~ r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4))
                      | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X2,X0,sK1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f42,f41,f40,f39,f38])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1891,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1896,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2922,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1891,c_1896])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1894,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3104,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2922,c_1894])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1897,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3004,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1891,c_1897])).

cnf(c_3420,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3104,c_3004])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1905,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3424,plain,
    ( k9_relat_1(sK2,sK3) = sK4
    | r1_tarski(sK4,k9_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3420,c_1905])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2109,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2195,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_2196,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2195])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_471,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_473,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1898,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2775,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1891,c_1898])).

cnf(c_3016,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_473,c_2775])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_390,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_3272,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3016,c_390])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_400,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_401,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1889,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_3279,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3272,c_1889])).

cnf(c_1901,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2299,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_1901])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_223])).

cnf(c_1890,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_2696,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1890])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1900,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3776,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2696,c_1900])).

cnf(c_4577,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3279,c_3776])).

cnf(c_4578,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4577])).

cnf(c_4590,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3420,c_4578])).

cnf(c_4933,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_35,c_2196,c_4590])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_418,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_419,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1888,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1899,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1987,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1899,c_1890])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1903,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4107,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k9_relat_1(X3,X1),X4) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X4) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_1903])).

cnf(c_13799,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top
    | r1_tarski(X2,sK2) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_4107])).

cnf(c_15391,plain,
    ( r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top
    | r1_tarski(X2,sK2) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13799,c_3776])).

cnf(c_15392,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top
    | r1_tarski(X2,sK2) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_15391])).

cnf(c_15404,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k9_relat_1(X0,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4933,c_15392])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1895,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3105,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2922,c_1895])).

cnf(c_3268,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3105,c_3004])).

cnf(c_4941,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4933,c_3268])).

cnf(c_16224,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15404,c_4941])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9995,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9998,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9995])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16224,c_9998])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.49/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.99  
% 3.49/0.99  ------  iProver source info
% 3.49/0.99  
% 3.49/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.99  git: non_committed_changes: false
% 3.49/0.99  git: last_make_outside_of_git: false
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options
% 3.49/0.99  
% 3.49/0.99  --out_options                           all
% 3.49/0.99  --tptp_safe_out                         true
% 3.49/0.99  --problem_path                          ""
% 3.49/0.99  --include_path                          ""
% 3.49/0.99  --clausifier                            res/vclausify_rel
% 3.49/0.99  --clausifier_options                    --mode clausify
% 3.49/0.99  --stdin                                 false
% 3.49/0.99  --stats_out                             all
% 3.49/0.99  
% 3.49/0.99  ------ General Options
% 3.49/0.99  
% 3.49/0.99  --fof                                   false
% 3.49/0.99  --time_out_real                         305.
% 3.49/0.99  --time_out_virtual                      -1.
% 3.49/0.99  --symbol_type_check                     false
% 3.49/0.99  --clausify_out                          false
% 3.49/0.99  --sig_cnt_out                           false
% 3.49/0.99  --trig_cnt_out                          false
% 3.49/0.99  --trig_cnt_out_tolerance                1.
% 3.49/0.99  --trig_cnt_out_sk_spl                   false
% 3.49/0.99  --abstr_cl_out                          false
% 3.49/0.99  
% 3.49/0.99  ------ Global Options
% 3.49/0.99  
% 3.49/0.99  --schedule                              default
% 3.49/0.99  --add_important_lit                     false
% 3.49/0.99  --prop_solver_per_cl                    1000
% 3.49/0.99  --min_unsat_core                        false
% 3.49/0.99  --soft_assumptions                      false
% 3.49/0.99  --soft_lemma_size                       3
% 3.49/0.99  --prop_impl_unit_size                   0
% 3.49/0.99  --prop_impl_unit                        []
% 3.49/0.99  --share_sel_clauses                     true
% 3.49/0.99  --reset_solvers                         false
% 3.49/0.99  --bc_imp_inh                            [conj_cone]
% 3.49/0.99  --conj_cone_tolerance                   3.
% 3.49/0.99  --extra_neg_conj                        none
% 3.49/0.99  --large_theory_mode                     true
% 3.49/0.99  --prolific_symb_bound                   200
% 3.49/0.99  --lt_threshold                          2000
% 3.49/0.99  --clause_weak_htbl                      true
% 3.49/0.99  --gc_record_bc_elim                     false
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing Options
% 3.49/0.99  
% 3.49/0.99  --preprocessing_flag                    true
% 3.49/0.99  --time_out_prep_mult                    0.1
% 3.49/0.99  --splitting_mode                        input
% 3.49/0.99  --splitting_grd                         true
% 3.49/0.99  --splitting_cvd                         false
% 3.49/0.99  --splitting_cvd_svl                     false
% 3.49/0.99  --splitting_nvd                         32
% 3.49/0.99  --sub_typing                            true
% 3.49/0.99  --prep_gs_sim                           true
% 3.49/0.99  --prep_unflatten                        true
% 3.49/0.99  --prep_res_sim                          true
% 3.49/0.99  --prep_upred                            true
% 3.49/0.99  --prep_sem_filter                       exhaustive
% 3.49/0.99  --prep_sem_filter_out                   false
% 3.49/0.99  --pred_elim                             true
% 3.49/0.99  --res_sim_input                         true
% 3.49/0.99  --eq_ax_congr_red                       true
% 3.49/0.99  --pure_diseq_elim                       true
% 3.49/0.99  --brand_transform                       false
% 3.49/0.99  --non_eq_to_eq                          false
% 3.49/0.99  --prep_def_merge                        true
% 3.49/0.99  --prep_def_merge_prop_impl              false
% 3.49/0.99  --prep_def_merge_mbd                    true
% 3.49/0.99  --prep_def_merge_tr_red                 false
% 3.49/0.99  --prep_def_merge_tr_cl                  false
% 3.49/0.99  --smt_preprocessing                     true
% 3.49/0.99  --smt_ac_axioms                         fast
% 3.49/0.99  --preprocessed_out                      false
% 3.49/0.99  --preprocessed_stats                    false
% 3.49/0.99  
% 3.49/0.99  ------ Abstraction refinement Options
% 3.49/0.99  
% 3.49/0.99  --abstr_ref                             []
% 3.49/0.99  --abstr_ref_prep                        false
% 3.49/0.99  --abstr_ref_until_sat                   false
% 3.49/0.99  --abstr_ref_sig_restrict                funpre
% 3.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.99  --abstr_ref_under                       []
% 3.49/0.99  
% 3.49/0.99  ------ SAT Options
% 3.49/0.99  
% 3.49/0.99  --sat_mode                              false
% 3.49/0.99  --sat_fm_restart_options                ""
% 3.49/0.99  --sat_gr_def                            false
% 3.49/0.99  --sat_epr_types                         true
% 3.49/0.99  --sat_non_cyclic_types                  false
% 3.49/0.99  --sat_finite_models                     false
% 3.49/0.99  --sat_fm_lemmas                         false
% 3.49/0.99  --sat_fm_prep                           false
% 3.49/0.99  --sat_fm_uc_incr                        true
% 3.49/0.99  --sat_out_model                         small
% 3.49/0.99  --sat_out_clauses                       false
% 3.49/0.99  
% 3.49/0.99  ------ QBF Options
% 3.49/0.99  
% 3.49/0.99  --qbf_mode                              false
% 3.49/0.99  --qbf_elim_univ                         false
% 3.49/0.99  --qbf_dom_inst                          none
% 3.49/0.99  --qbf_dom_pre_inst                      false
% 3.49/0.99  --qbf_sk_in                             false
% 3.49/0.99  --qbf_pred_elim                         true
% 3.49/0.99  --qbf_split                             512
% 3.49/0.99  
% 3.49/0.99  ------ BMC1 Options
% 3.49/0.99  
% 3.49/0.99  --bmc1_incremental                      false
% 3.49/0.99  --bmc1_axioms                           reachable_all
% 3.49/0.99  --bmc1_min_bound                        0
% 3.49/0.99  --bmc1_max_bound                        -1
% 3.49/0.99  --bmc1_max_bound_default                -1
% 3.49/0.99  --bmc1_symbol_reachability              true
% 3.49/0.99  --bmc1_property_lemmas                  false
% 3.49/0.99  --bmc1_k_induction                      false
% 3.49/0.99  --bmc1_non_equiv_states                 false
% 3.49/0.99  --bmc1_deadlock                         false
% 3.49/0.99  --bmc1_ucm                              false
% 3.49/0.99  --bmc1_add_unsat_core                   none
% 3.49/0.99  --bmc1_unsat_core_children              false
% 3.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.99  --bmc1_out_stat                         full
% 3.49/0.99  --bmc1_ground_init                      false
% 3.49/0.99  --bmc1_pre_inst_next_state              false
% 3.49/0.99  --bmc1_pre_inst_state                   false
% 3.49/0.99  --bmc1_pre_inst_reach_state             false
% 3.49/0.99  --bmc1_out_unsat_core                   false
% 3.49/0.99  --bmc1_aig_witness_out                  false
% 3.49/0.99  --bmc1_verbose                          false
% 3.49/0.99  --bmc1_dump_clauses_tptp                false
% 3.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.99  --bmc1_dump_file                        -
% 3.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.99  --bmc1_ucm_extend_mode                  1
% 3.49/0.99  --bmc1_ucm_init_mode                    2
% 3.49/0.99  --bmc1_ucm_cone_mode                    none
% 3.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.99  --bmc1_ucm_relax_model                  4
% 3.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.99  --bmc1_ucm_layered_model                none
% 3.49/0.99  --bmc1_ucm_max_lemma_size               10
% 3.49/0.99  
% 3.49/0.99  ------ AIG Options
% 3.49/0.99  
% 3.49/0.99  --aig_mode                              false
% 3.49/0.99  
% 3.49/0.99  ------ Instantiation Options
% 3.49/0.99  
% 3.49/0.99  --instantiation_flag                    true
% 3.49/0.99  --inst_sos_flag                         false
% 3.49/0.99  --inst_sos_phase                        true
% 3.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel_side                     num_symb
% 3.49/0.99  --inst_solver_per_active                1400
% 3.49/0.99  --inst_solver_calls_frac                1.
% 3.49/0.99  --inst_passive_queue_type               priority_queues
% 3.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.99  --inst_passive_queues_freq              [25;2]
% 3.49/0.99  --inst_dismatching                      true
% 3.49/0.99  --inst_eager_unprocessed_to_passive     true
% 3.49/0.99  --inst_prop_sim_given                   true
% 3.49/0.99  --inst_prop_sim_new                     false
% 3.49/0.99  --inst_subs_new                         false
% 3.49/0.99  --inst_eq_res_simp                      false
% 3.49/0.99  --inst_subs_given                       false
% 3.49/0.99  --inst_orphan_elimination               true
% 3.49/0.99  --inst_learning_loop_flag               true
% 3.49/0.99  --inst_learning_start                   3000
% 3.49/0.99  --inst_learning_factor                  2
% 3.49/0.99  --inst_start_prop_sim_after_learn       3
% 3.49/0.99  --inst_sel_renew                        solver
% 3.49/0.99  --inst_lit_activity_flag                true
% 3.49/0.99  --inst_restr_to_given                   false
% 3.49/0.99  --inst_activity_threshold               500
% 3.49/0.99  --inst_out_proof                        true
% 3.49/0.99  
% 3.49/0.99  ------ Resolution Options
% 3.49/0.99  
% 3.49/0.99  --resolution_flag                       true
% 3.49/0.99  --res_lit_sel                           adaptive
% 3.49/0.99  --res_lit_sel_side                      none
% 3.49/0.99  --res_ordering                          kbo
% 3.49/0.99  --res_to_prop_solver                    active
% 3.49/0.99  --res_prop_simpl_new                    false
% 3.49/0.99  --res_prop_simpl_given                  true
% 3.49/0.99  --res_passive_queue_type                priority_queues
% 3.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.99  --res_passive_queues_freq               [15;5]
% 3.49/0.99  --res_forward_subs                      full
% 3.49/0.99  --res_backward_subs                     full
% 3.49/0.99  --res_forward_subs_resolution           true
% 3.49/0.99  --res_backward_subs_resolution          true
% 3.49/0.99  --res_orphan_elimination                true
% 3.49/0.99  --res_time_limit                        2.
% 3.49/0.99  --res_out_proof                         true
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Options
% 3.49/0.99  
% 3.49/0.99  --superposition_flag                    true
% 3.49/0.99  --sup_passive_queue_type                priority_queues
% 3.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.99  --demod_completeness_check              fast
% 3.49/0.99  --demod_use_ground                      true
% 3.49/0.99  --sup_to_prop_solver                    passive
% 3.49/0.99  --sup_prop_simpl_new                    true
% 3.49/0.99  --sup_prop_simpl_given                  true
% 3.49/0.99  --sup_fun_splitting                     false
% 3.49/0.99  --sup_smt_interval                      50000
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Simplification Setup
% 3.49/0.99  
% 3.49/0.99  --sup_indices_passive                   []
% 3.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_full_bw                           [BwDemod]
% 3.49/0.99  --sup_immed_triv                        [TrivRules]
% 3.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_immed_bw_main                     []
% 3.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.99  
% 3.49/0.99  ------ Combination Options
% 3.49/0.99  
% 3.49/0.99  --comb_res_mult                         3
% 3.49/0.99  --comb_sup_mult                         2
% 3.49/0.99  --comb_inst_mult                        10
% 3.49/0.99  
% 3.49/0.99  ------ Debug Options
% 3.49/0.99  
% 3.49/0.99  --dbg_backtrace                         false
% 3.49/0.99  --dbg_dump_prop_clauses                 false
% 3.49/0.99  --dbg_dump_prop_clauses_file            -
% 3.49/0.99  --dbg_out_stat                          false
% 3.49/0.99  ------ Parsing...
% 3.49/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.99  ------ Proving...
% 3.49/0.99  ------ Problem Properties 
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  clauses                                 21
% 3.49/0.99  conjectures                             5
% 3.49/0.99  EPR                                     6
% 3.49/0.99  Horn                                    19
% 3.49/0.99  unary                                   7
% 3.49/0.99  binary                                  9
% 3.49/0.99  lits                                    43
% 3.49/0.99  lits eq                                 8
% 3.49/0.99  fd_pure                                 0
% 3.49/0.99  fd_pseudo                               0
% 3.49/0.99  fd_cond                                 0
% 3.49/0.99  fd_pseudo_cond                          1
% 3.49/0.99  AC symbols                              0
% 3.49/0.99  
% 3.49/0.99  ------ Schedule dynamic 5 is on 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  Current options:
% 3.49/0.99  ------ 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options
% 3.49/0.99  
% 3.49/0.99  --out_options                           all
% 3.49/0.99  --tptp_safe_out                         true
% 3.49/0.99  --problem_path                          ""
% 3.49/0.99  --include_path                          ""
% 3.49/0.99  --clausifier                            res/vclausify_rel
% 3.49/0.99  --clausifier_options                    --mode clausify
% 3.49/0.99  --stdin                                 false
% 3.49/0.99  --stats_out                             all
% 3.49/0.99  
% 3.49/0.99  ------ General Options
% 3.49/0.99  
% 3.49/0.99  --fof                                   false
% 3.49/0.99  --time_out_real                         305.
% 3.49/0.99  --time_out_virtual                      -1.
% 3.49/0.99  --symbol_type_check                     false
% 3.49/0.99  --clausify_out                          false
% 3.49/0.99  --sig_cnt_out                           false
% 3.49/0.99  --trig_cnt_out                          false
% 3.49/0.99  --trig_cnt_out_tolerance                1.
% 3.49/0.99  --trig_cnt_out_sk_spl                   false
% 3.49/0.99  --abstr_cl_out                          false
% 3.49/0.99  
% 3.49/0.99  ------ Global Options
% 3.49/0.99  
% 3.49/0.99  --schedule                              default
% 3.49/0.99  --add_important_lit                     false
% 3.49/0.99  --prop_solver_per_cl                    1000
% 3.49/0.99  --min_unsat_core                        false
% 3.49/0.99  --soft_assumptions                      false
% 3.49/0.99  --soft_lemma_size                       3
% 3.49/0.99  --prop_impl_unit_size                   0
% 3.49/0.99  --prop_impl_unit                        []
% 3.49/0.99  --share_sel_clauses                     true
% 3.49/0.99  --reset_solvers                         false
% 3.49/0.99  --bc_imp_inh                            [conj_cone]
% 3.49/0.99  --conj_cone_tolerance                   3.
% 3.49/0.99  --extra_neg_conj                        none
% 3.49/0.99  --large_theory_mode                     true
% 3.49/0.99  --prolific_symb_bound                   200
% 3.49/0.99  --lt_threshold                          2000
% 3.49/0.99  --clause_weak_htbl                      true
% 3.49/0.99  --gc_record_bc_elim                     false
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing Options
% 3.49/0.99  
% 3.49/0.99  --preprocessing_flag                    true
% 3.49/0.99  --time_out_prep_mult                    0.1
% 3.49/0.99  --splitting_mode                        input
% 3.49/0.99  --splitting_grd                         true
% 3.49/0.99  --splitting_cvd                         false
% 3.49/0.99  --splitting_cvd_svl                     false
% 3.49/0.99  --splitting_nvd                         32
% 3.49/0.99  --sub_typing                            true
% 3.49/0.99  --prep_gs_sim                           true
% 3.49/0.99  --prep_unflatten                        true
% 3.49/0.99  --prep_res_sim                          true
% 3.49/0.99  --prep_upred                            true
% 3.49/0.99  --prep_sem_filter                       exhaustive
% 3.49/0.99  --prep_sem_filter_out                   false
% 3.49/0.99  --pred_elim                             true
% 3.49/0.99  --res_sim_input                         true
% 3.49/0.99  --eq_ax_congr_red                       true
% 3.49/0.99  --pure_diseq_elim                       true
% 3.49/0.99  --brand_transform                       false
% 3.49/0.99  --non_eq_to_eq                          false
% 3.49/0.99  --prep_def_merge                        true
% 3.49/0.99  --prep_def_merge_prop_impl              false
% 3.49/0.99  --prep_def_merge_mbd                    true
% 3.49/0.99  --prep_def_merge_tr_red                 false
% 3.49/0.99  --prep_def_merge_tr_cl                  false
% 3.49/0.99  --smt_preprocessing                     true
% 3.49/0.99  --smt_ac_axioms                         fast
% 3.49/0.99  --preprocessed_out                      false
% 3.49/0.99  --preprocessed_stats                    false
% 3.49/0.99  
% 3.49/0.99  ------ Abstraction refinement Options
% 3.49/0.99  
% 3.49/0.99  --abstr_ref                             []
% 3.49/0.99  --abstr_ref_prep                        false
% 3.49/0.99  --abstr_ref_until_sat                   false
% 3.49/0.99  --abstr_ref_sig_restrict                funpre
% 3.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.99  --abstr_ref_under                       []
% 3.49/0.99  
% 3.49/0.99  ------ SAT Options
% 3.49/0.99  
% 3.49/0.99  --sat_mode                              false
% 3.49/0.99  --sat_fm_restart_options                ""
% 3.49/0.99  --sat_gr_def                            false
% 3.49/0.99  --sat_epr_types                         true
% 3.49/0.99  --sat_non_cyclic_types                  false
% 3.49/0.99  --sat_finite_models                     false
% 3.49/0.99  --sat_fm_lemmas                         false
% 3.49/0.99  --sat_fm_prep                           false
% 3.49/0.99  --sat_fm_uc_incr                        true
% 3.49/0.99  --sat_out_model                         small
% 3.49/0.99  --sat_out_clauses                       false
% 3.49/0.99  
% 3.49/0.99  ------ QBF Options
% 3.49/0.99  
% 3.49/0.99  --qbf_mode                              false
% 3.49/0.99  --qbf_elim_univ                         false
% 3.49/0.99  --qbf_dom_inst                          none
% 3.49/0.99  --qbf_dom_pre_inst                      false
% 3.49/0.99  --qbf_sk_in                             false
% 3.49/0.99  --qbf_pred_elim                         true
% 3.49/0.99  --qbf_split                             512
% 3.49/0.99  
% 3.49/0.99  ------ BMC1 Options
% 3.49/0.99  
% 3.49/0.99  --bmc1_incremental                      false
% 3.49/0.99  --bmc1_axioms                           reachable_all
% 3.49/0.99  --bmc1_min_bound                        0
% 3.49/0.99  --bmc1_max_bound                        -1
% 3.49/0.99  --bmc1_max_bound_default                -1
% 3.49/0.99  --bmc1_symbol_reachability              true
% 3.49/0.99  --bmc1_property_lemmas                  false
% 3.49/0.99  --bmc1_k_induction                      false
% 3.49/0.99  --bmc1_non_equiv_states                 false
% 3.49/0.99  --bmc1_deadlock                         false
% 3.49/0.99  --bmc1_ucm                              false
% 3.49/0.99  --bmc1_add_unsat_core                   none
% 3.49/0.99  --bmc1_unsat_core_children              false
% 3.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.99  --bmc1_out_stat                         full
% 3.49/0.99  --bmc1_ground_init                      false
% 3.49/0.99  --bmc1_pre_inst_next_state              false
% 3.49/0.99  --bmc1_pre_inst_state                   false
% 3.49/0.99  --bmc1_pre_inst_reach_state             false
% 3.49/0.99  --bmc1_out_unsat_core                   false
% 3.49/0.99  --bmc1_aig_witness_out                  false
% 3.49/0.99  --bmc1_verbose                          false
% 3.49/0.99  --bmc1_dump_clauses_tptp                false
% 3.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.99  --bmc1_dump_file                        -
% 3.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.99  --bmc1_ucm_extend_mode                  1
% 3.49/0.99  --bmc1_ucm_init_mode                    2
% 3.49/0.99  --bmc1_ucm_cone_mode                    none
% 3.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.99  --bmc1_ucm_relax_model                  4
% 3.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.99  --bmc1_ucm_layered_model                none
% 3.49/0.99  --bmc1_ucm_max_lemma_size               10
% 3.49/0.99  
% 3.49/0.99  ------ AIG Options
% 3.49/0.99  
% 3.49/0.99  --aig_mode                              false
% 3.49/0.99  
% 3.49/0.99  ------ Instantiation Options
% 3.49/0.99  
% 3.49/0.99  --instantiation_flag                    true
% 3.49/0.99  --inst_sos_flag                         false
% 3.49/0.99  --inst_sos_phase                        true
% 3.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel_side                     none
% 3.49/0.99  --inst_solver_per_active                1400
% 3.49/0.99  --inst_solver_calls_frac                1.
% 3.49/0.99  --inst_passive_queue_type               priority_queues
% 3.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.99  --inst_passive_queues_freq              [25;2]
% 3.49/0.99  --inst_dismatching                      true
% 3.49/0.99  --inst_eager_unprocessed_to_passive     true
% 3.49/0.99  --inst_prop_sim_given                   true
% 3.49/0.99  --inst_prop_sim_new                     false
% 3.49/0.99  --inst_subs_new                         false
% 3.49/0.99  --inst_eq_res_simp                      false
% 3.49/0.99  --inst_subs_given                       false
% 3.49/0.99  --inst_orphan_elimination               true
% 3.49/0.99  --inst_learning_loop_flag               true
% 3.49/0.99  --inst_learning_start                   3000
% 3.49/0.99  --inst_learning_factor                  2
% 3.49/0.99  --inst_start_prop_sim_after_learn       3
% 3.49/0.99  --inst_sel_renew                        solver
% 3.49/0.99  --inst_lit_activity_flag                true
% 3.49/0.99  --inst_restr_to_given                   false
% 3.49/0.99  --inst_activity_threshold               500
% 3.49/0.99  --inst_out_proof                        true
% 3.49/0.99  
% 3.49/0.99  ------ Resolution Options
% 3.49/0.99  
% 3.49/0.99  --resolution_flag                       false
% 3.49/0.99  --res_lit_sel                           adaptive
% 3.49/0.99  --res_lit_sel_side                      none
% 3.49/0.99  --res_ordering                          kbo
% 3.49/0.99  --res_to_prop_solver                    active
% 3.49/0.99  --res_prop_simpl_new                    false
% 3.49/0.99  --res_prop_simpl_given                  true
% 3.49/0.99  --res_passive_queue_type                priority_queues
% 3.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.99  --res_passive_queues_freq               [15;5]
% 3.49/0.99  --res_forward_subs                      full
% 3.49/0.99  --res_backward_subs                     full
% 3.49/0.99  --res_forward_subs_resolution           true
% 3.49/0.99  --res_backward_subs_resolution          true
% 3.49/0.99  --res_orphan_elimination                true
% 3.49/0.99  --res_time_limit                        2.
% 3.49/0.99  --res_out_proof                         true
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Options
% 3.49/0.99  
% 3.49/0.99  --superposition_flag                    true
% 3.49/0.99  --sup_passive_queue_type                priority_queues
% 3.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.99  --demod_completeness_check              fast
% 3.49/0.99  --demod_use_ground                      true
% 3.49/0.99  --sup_to_prop_solver                    passive
% 3.49/0.99  --sup_prop_simpl_new                    true
% 3.49/0.99  --sup_prop_simpl_given                  true
% 3.49/0.99  --sup_fun_splitting                     false
% 3.49/0.99  --sup_smt_interval                      50000
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Simplification Setup
% 3.49/0.99  
% 3.49/0.99  --sup_indices_passive                   []
% 3.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_full_bw                           [BwDemod]
% 3.49/0.99  --sup_immed_triv                        [TrivRules]
% 3.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_immed_bw_main                     []
% 3.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.99  
% 3.49/0.99  ------ Combination Options
% 3.49/0.99  
% 3.49/0.99  --comb_res_mult                         3
% 3.49/0.99  --comb_sup_mult                         2
% 3.49/0.99  --comb_inst_mult                        10
% 3.49/0.99  
% 3.49/0.99  ------ Debug Options
% 3.49/0.99  
% 3.49/0.99  --dbg_backtrace                         false
% 3.49/0.99  --dbg_dump_prop_clauses                 false
% 3.49/0.99  --dbg_dump_prop_clauses_file            -
% 3.49/0.99  --dbg_out_stat                          false
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ Proving...
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  % SZS status Theorem for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  fof(f14,conjecture,(
% 3.49/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f15,negated_conjecture,(
% 3.49/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.49/0.99    inference(negated_conjecture,[],[f14])).
% 3.49/0.99  
% 3.49/0.99  fof(f30,plain,(
% 3.49/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.49/0.99    inference(ennf_transformation,[],[f15])).
% 3.49/0.99  
% 3.49/0.99  fof(f31,plain,(
% 3.49/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.49/0.99    inference(flattening,[],[f30])).
% 3.49/0.99  
% 3.49/0.99  fof(f36,plain,(
% 3.49/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.49/0.99    inference(nnf_transformation,[],[f31])).
% 3.49/0.99  
% 3.49/0.99  fof(f37,plain,(
% 3.49/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.49/0.99    inference(flattening,[],[f36])).
% 3.49/0.99  
% 3.49/0.99  fof(f42,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f41,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f40,plain,(
% 3.49/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f39,plain,(
% 3.49/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f38,plain,(
% 3.49/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f43,plain,(
% 3.49/0.99    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f42,f41,f40,f39,f38])).
% 3.49/0.99  
% 3.49/0.99  fof(f69,plain,(
% 3.49/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f12,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f27,plain,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f12])).
% 3.49/0.99  
% 3.49/0.99  fof(f58,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f27])).
% 3.49/0.99  
% 3.49/0.99  fof(f72,plain,(
% 3.49/0.99    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f11,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f26,plain,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f11])).
% 3.49/0.99  
% 3.49/0.99  fof(f57,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f26])).
% 3.49/0.99  
% 3.49/0.99  fof(f2,axiom,(
% 3.49/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f32,plain,(
% 3.49/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.99    inference(nnf_transformation,[],[f2])).
% 3.49/0.99  
% 3.49/0.99  fof(f33,plain,(
% 3.49/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.99    inference(flattening,[],[f32])).
% 3.49/0.99  
% 3.49/0.99  fof(f47,plain,(
% 3.49/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f33])).
% 3.49/0.99  
% 3.49/0.99  fof(f70,plain,(
% 3.49/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f4,axiom,(
% 3.49/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f34,plain,(
% 3.49/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.49/0.99    inference(nnf_transformation,[],[f4])).
% 3.49/0.99  
% 3.49/0.99  fof(f49,plain,(
% 3.49/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f34])).
% 3.49/0.99  
% 3.49/0.99  fof(f13,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f28,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f13])).
% 3.49/0.99  
% 3.49/0.99  fof(f29,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(flattening,[],[f28])).
% 3.49/0.99  
% 3.49/0.99  fof(f35,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(nnf_transformation,[],[f29])).
% 3.49/0.99  
% 3.49/0.99  fof(f59,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f35])).
% 3.49/0.99  
% 3.49/0.99  fof(f68,plain,(
% 3.49/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f10,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f25,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f10])).
% 3.49/0.99  
% 3.49/0.99  fof(f56,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f25])).
% 3.49/0.99  
% 3.49/0.99  fof(f1,axiom,(
% 3.49/0.99    v1_xboole_0(k1_xboole_0)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f44,plain,(
% 3.49/0.99    v1_xboole_0(k1_xboole_0)),
% 3.49/0.99    inference(cnf_transformation,[],[f1])).
% 3.49/0.99  
% 3.49/0.99  fof(f66,plain,(
% 3.49/0.99    ~v1_xboole_0(sK1)),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f9,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f23,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.49/0.99    inference(ennf_transformation,[],[f9])).
% 3.49/0.99  
% 3.49/0.99  fof(f24,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(flattening,[],[f23])).
% 3.49/0.99  
% 3.49/0.99  fof(f55,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f24])).
% 3.49/0.99  
% 3.49/0.99  fof(f67,plain,(
% 3.49/0.99    v1_funct_1(sK2)),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f5,axiom,(
% 3.49/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f18,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.49/0.99    inference(ennf_transformation,[],[f5])).
% 3.49/0.99  
% 3.49/0.99  fof(f51,plain,(
% 3.49/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f18])).
% 3.49/0.99  
% 3.49/0.99  fof(f50,plain,(
% 3.49/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f34])).
% 3.49/0.99  
% 3.49/0.99  fof(f6,axiom,(
% 3.49/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f52,plain,(
% 3.49/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f6])).
% 3.49/0.99  
% 3.49/0.99  fof(f8,axiom,(
% 3.49/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f21,plain,(
% 3.49/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.49/0.99    inference(ennf_transformation,[],[f8])).
% 3.49/0.99  
% 3.49/0.99  fof(f22,plain,(
% 3.49/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.49/0.99    inference(flattening,[],[f21])).
% 3.49/0.99  
% 3.49/0.99  fof(f54,plain,(
% 3.49/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f22])).
% 3.49/0.99  
% 3.49/0.99  fof(f7,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f19,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(ennf_transformation,[],[f7])).
% 3.49/0.99  
% 3.49/0.99  fof(f20,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(flattening,[],[f19])).
% 3.49/0.99  
% 3.49/0.99  fof(f53,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f20])).
% 3.49/0.99  
% 3.49/0.99  fof(f3,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f16,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.49/0.99    inference(ennf_transformation,[],[f3])).
% 3.49/0.99  
% 3.49/0.99  fof(f17,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.49/0.99    inference(flattening,[],[f16])).
% 3.49/0.99  
% 3.49/0.99  fof(f48,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f17])).
% 3.49/0.99  
% 3.49/0.99  fof(f73,plain,(
% 3.49/0.99    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.49/0.99    inference(cnf_transformation,[],[f43])).
% 3.49/0.99  
% 3.49/0.99  fof(f45,plain,(
% 3.49/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.49/0.99    inference(cnf_transformation,[],[f33])).
% 3.49/0.99  
% 3.49/0.99  fof(f75,plain,(
% 3.49/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.49/0.99    inference(equality_resolution,[],[f45])).
% 3.49/0.99  
% 3.49/0.99  cnf(c_25,negated_conjecture,
% 3.49/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.49/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1891,plain,
% 3.49/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_14,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.49/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1896,plain,
% 3.49/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2922,plain,
% 3.49/0.99      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1891,c_1896]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_22,negated_conjecture,
% 3.49/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.49/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.49/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1894,plain,
% 3.49/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 3.49/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3104,plain,
% 3.49/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 3.49/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_2922,c_1894]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_13,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.49/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1897,plain,
% 3.49/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3004,plain,
% 3.49/0.99      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1891,c_1897]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3420,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 3.49/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_3104,c_3004]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1,plain,
% 3.49/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.49/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1905,plain,
% 3.49/0.99      ( X0 = X1
% 3.49/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3424,plain,
% 3.49/0.99      ( k9_relat_1(sK2,sK3) = sK4
% 3.49/0.99      | r1_tarski(sK4,k9_relat_1(sK2,sK3)) != iProver_top
% 3.49/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_3420,c_1905]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_24,negated_conjecture,
% 3.49/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.49/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_35,plain,
% 3.49/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_6,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2109,plain,
% 3.49/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2195,plain,
% 3.49/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) | r1_tarski(sK3,sK0) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_2109]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2196,plain,
% 3.49/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.49/0.99      | r1_tarski(sK3,sK0) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2195]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_20,plain,
% 3.49/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.49/0.99      | k1_xboole_0 = X2 ),
% 3.49/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_26,negated_conjecture,
% 3.49/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_470,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.49/0.99      | sK2 != X0
% 3.49/0.99      | sK1 != X2
% 3.49/0.99      | sK0 != X1
% 3.49/0.99      | k1_xboole_0 = X2 ),
% 3.49/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_471,plain,
% 3.49/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.49/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.49/0.99      | k1_xboole_0 = sK1 ),
% 3.49/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_473,plain,
% 3.49/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_471,c_25]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_12,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1898,plain,
% 3.49/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2775,plain,
% 3.49/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1891,c_1898]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3016,plain,
% 3.49/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_473,c_2775]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_0,plain,
% 3.49/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_28,negated_conjecture,
% 3.49/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_390,plain,
% 3.49/0.99      ( sK1 != k1_xboole_0 ),
% 3.49/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3272,plain,
% 3.49/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_3016,c_390]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_11,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.49/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.49/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.49/0.99      | ~ v1_funct_1(X1)
% 3.49/0.99      | ~ v1_relat_1(X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_27,negated_conjecture,
% 3.49/0.99      ( v1_funct_1(sK2) ),
% 3.49/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_400,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.49/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.49/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.49/0.99      | ~ v1_relat_1(X1)
% 3.49/0.99      | sK2 != X1 ),
% 3.49/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_401,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 3.49/0.99      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.49/0.99      | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 3.49/0.99      | ~ v1_relat_1(sK2) ),
% 3.49/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1889,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.49/0.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.49/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3279,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.49/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.49/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_3272,c_1889]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1901,plain,
% 3.49/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.49/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2299,plain,
% 3.49/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1891,c_1901]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/0.99      | ~ v1_relat_1(X1)
% 3.49/0.99      | v1_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_5,plain,
% 3.49/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_222,plain,
% 3.49/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.49/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_223,plain,
% 3.49/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.49/0.99      inference(renaming,[status(thm)],[c_222]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_285,plain,
% 3.49/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.49/0.99      inference(bin_hyper_res,[status(thm)],[c_7,c_223]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1890,plain,
% 3.49/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | v1_relat_1(X1) != iProver_top
% 3.49/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2696,plain,
% 3.49/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.49/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_2299,c_1890]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_8,plain,
% 3.49/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.49/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1900,plain,
% 3.49/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3776,plain,
% 3.49/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.49/0.99      inference(forward_subsumption_resolution,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_2696,c_1900]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4577,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.49/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.49/0.99      | r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_3279,c_3776]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4578,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.49/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
% 3.49/0.99      inference(renaming,[status(thm)],[c_4577]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4590,plain,
% 3.49/0.99      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 3.49/0.99      | r1_tarski(sK3,sK0) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_3420,c_4578]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4933,plain,
% 3.49/0.99      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_3424,c_35,c_2196,c_4590]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_10,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.49/0.99      | ~ v1_funct_1(X0)
% 3.49/0.99      | ~ v1_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_418,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.49/0.99      | ~ v1_relat_1(X0)
% 3.49/0.99      | sK2 != X0 ),
% 3.49/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_419,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 3.49/0.99      | ~ v1_relat_1(sK2) ),
% 3.49/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1888,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
% 3.49/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_9,plain,
% 3.49/0.99      ( ~ r1_tarski(X0,X1)
% 3.49/0.99      | ~ r1_tarski(X2,X3)
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
% 3.49/0.99      | ~ v1_relat_1(X3)
% 3.49/0.99      | ~ v1_relat_1(X2) ),
% 3.49/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1899,plain,
% 3.49/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) = iProver_top
% 3.49/0.99      | v1_relat_1(X3) != iProver_top
% 3.49/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1987,plain,
% 3.49/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) = iProver_top
% 3.49/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.49/0.99      inference(forward_subsumption_resolution,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_1899,c_1890]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4,plain,
% 3.49/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.49/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1903,plain,
% 3.49/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.49/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4107,plain,
% 3.49/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X3,X1),X4) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),X4) = iProver_top
% 3.49/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1987,c_1903]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_13799,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top
% 3.49/0.99      | r1_tarski(X2,sK2) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top
% 3.49/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1888,c_4107]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_15391,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top
% 3.49/0.99      | r1_tarski(X2,sK2) != iProver_top
% 3.49/0.99      | r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_13799,c_3776]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_15392,plain,
% 3.49/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top
% 3.49/0.99      | r1_tarski(X2,sK2) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X2,X0),X1) = iProver_top ),
% 3.49/0.99      inference(renaming,[status(thm)],[c_15391]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_15404,plain,
% 3.49/0.99      ( r1_tarski(X0,sK2) != iProver_top
% 3.49/0.99      | r1_tarski(k9_relat_1(X0,sK3),sK4) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_4933,c_15392]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_21,negated_conjecture,
% 3.49/0.99      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.49/0.99      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.49/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1895,plain,
% 3.49/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 3.49/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3105,plain,
% 3.49/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 3.49/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_2922,c_1895]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3268,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 3.49/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_3105,c_3004]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4941,plain,
% 3.49/0.99      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_4933,c_3268]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_16224,plain,
% 3.49/0.99      ( r1_tarski(sK2,sK2) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_15404,c_4941]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3,plain,
% 3.49/0.99      ( r1_tarski(X0,X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_9995,plain,
% 3.49/0.99      ( r1_tarski(sK2,sK2) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_9998,plain,
% 3.49/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_9995]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(contradiction,plain,
% 3.49/0.99      ( $false ),
% 3.49/0.99      inference(minisat,[status(thm)],[c_16224,c_9998]) ).
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  ------                               Statistics
% 3.49/0.99  
% 3.49/0.99  ------ General
% 3.49/0.99  
% 3.49/0.99  abstr_ref_over_cycles:                  0
% 3.49/0.99  abstr_ref_under_cycles:                 0
% 3.49/0.99  gc_basic_clause_elim:                   0
% 3.49/0.99  forced_gc_time:                         0
% 3.49/0.99  parsing_time:                           0.009
% 3.49/0.99  unif_index_cands_time:                  0.
% 3.49/0.99  unif_index_add_time:                    0.
% 3.49/0.99  orderings_time:                         0.
% 3.49/0.99  out_proof_time:                         0.009
% 3.49/0.99  total_time:                             0.404
% 3.49/0.99  num_of_symbols:                         51
% 3.49/0.99  num_of_terms:                           10091
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing
% 3.49/0.99  
% 3.49/0.99  num_of_splits:                          0
% 3.49/0.99  num_of_split_atoms:                     0
% 3.49/0.99  num_of_reused_defs:                     0
% 3.49/0.99  num_eq_ax_congr_red:                    9
% 3.49/0.99  num_of_sem_filtered_clauses:            1
% 3.49/0.99  num_of_subtypes:                        0
% 3.49/0.99  monotx_restored_types:                  0
% 3.49/0.99  sat_num_of_epr_types:                   0
% 3.49/0.99  sat_num_of_non_cyclic_types:            0
% 3.49/0.99  sat_guarded_non_collapsed_types:        0
% 3.49/0.99  num_pure_diseq_elim:                    0
% 3.49/0.99  simp_replaced_by:                       0
% 3.49/0.99  res_preprocessed:                       143
% 3.49/0.99  prep_upred:                             0
% 3.49/0.99  prep_unflattend:                        74
% 3.49/0.99  smt_new_axioms:                         0
% 3.49/0.99  pred_elim_cands:                        3
% 3.49/0.99  pred_elim:                              3
% 3.49/0.99  pred_elim_cl:                           8
% 3.49/0.99  pred_elim_cycles:                       7
% 3.49/0.99  merged_defs:                            20
% 3.49/0.99  merged_defs_ncl:                        0
% 3.49/0.99  bin_hyper_res:                          21
% 3.49/0.99  prep_cycles:                            5
% 3.49/0.99  pred_elim_time:                         0.014
% 3.49/0.99  splitting_time:                         0.
% 3.49/0.99  sem_filter_time:                        0.
% 3.49/0.99  monotx_time:                            0.
% 3.49/0.99  subtype_inf_time:                       0.
% 3.49/0.99  
% 3.49/0.99  ------ Problem properties
% 3.49/0.99  
% 3.49/0.99  clauses:                                21
% 3.49/0.99  conjectures:                            5
% 3.49/0.99  epr:                                    6
% 3.49/0.99  horn:                                   19
% 3.49/0.99  ground:                                 8
% 3.49/0.99  unary:                                  7
% 3.49/0.99  binary:                                 9
% 3.49/0.99  lits:                                   43
% 3.49/0.99  lits_eq:                                8
% 3.49/0.99  fd_pure:                                0
% 3.49/0.99  fd_pseudo:                              0
% 3.49/0.99  fd_cond:                                0
% 3.49/0.99  fd_pseudo_cond:                         1
% 3.49/0.99  ac_symbols:                             0
% 3.49/0.99  
% 3.49/0.99  ------ Propositional Solver
% 3.49/0.99  
% 3.49/0.99  prop_solver_calls:                      36
% 3.49/0.99  prop_fast_solver_calls:                 1299
% 3.49/0.99  smt_solver_calls:                       0
% 3.49/0.99  smt_fast_solver_calls:                  0
% 3.49/0.99  prop_num_of_clauses:                    5958
% 3.49/0.99  prop_preprocess_simplified:             10097
% 3.49/0.99  prop_fo_subsumed:                       41
% 3.49/0.99  prop_solver_time:                       0.
% 3.49/0.99  smt_solver_time:                        0.
% 3.49/0.99  smt_fast_solver_time:                   0.
% 3.49/0.99  prop_fast_solver_time:                  0.
% 3.49/0.99  prop_unsat_core_time:                   0.
% 3.49/0.99  
% 3.49/0.99  ------ QBF
% 3.49/0.99  
% 3.49/0.99  qbf_q_res:                              0
% 3.49/0.99  qbf_num_tautologies:                    0
% 3.49/0.99  qbf_prep_cycles:                        0
% 3.49/0.99  
% 3.49/0.99  ------ BMC1
% 3.49/0.99  
% 3.49/0.99  bmc1_current_bound:                     -1
% 3.49/0.99  bmc1_last_solved_bound:                 -1
% 3.49/0.99  bmc1_unsat_core_size:                   -1
% 3.49/0.99  bmc1_unsat_core_parents_size:           -1
% 3.49/0.99  bmc1_merge_next_fun:                    0
% 3.49/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.49/0.99  
% 3.49/0.99  ------ Instantiation
% 3.49/0.99  
% 3.49/0.99  inst_num_of_clauses:                    1468
% 3.49/0.99  inst_num_in_passive:                    377
% 3.49/0.99  inst_num_in_active:                     795
% 3.49/0.99  inst_num_in_unprocessed:                298
% 3.49/0.99  inst_num_of_loops:                      820
% 3.49/0.99  inst_num_of_learning_restarts:          0
% 3.49/0.99  inst_num_moves_active_passive:          19
% 3.49/0.99  inst_lit_activity:                      0
% 3.49/0.99  inst_lit_activity_moves:                0
% 3.49/0.99  inst_num_tautologies:                   0
% 3.49/0.99  inst_num_prop_implied:                  0
% 3.49/0.99  inst_num_existing_simplified:           0
% 3.49/0.99  inst_num_eq_res_simplified:             0
% 3.49/0.99  inst_num_child_elim:                    0
% 3.49/0.99  inst_num_of_dismatching_blockings:      494
% 3.49/0.99  inst_num_of_non_proper_insts:           2243
% 3.49/0.99  inst_num_of_duplicates:                 0
% 3.49/0.99  inst_inst_num_from_inst_to_res:         0
% 3.49/0.99  inst_dismatching_checking_time:         0.
% 3.49/0.99  
% 3.49/0.99  ------ Resolution
% 3.49/0.99  
% 3.49/0.99  res_num_of_clauses:                     0
% 3.49/0.99  res_num_in_passive:                     0
% 3.49/0.99  res_num_in_active:                      0
% 3.49/0.99  res_num_of_loops:                       148
% 3.49/0.99  res_forward_subset_subsumed:            153
% 3.49/0.99  res_backward_subset_subsumed:           12
% 3.49/0.99  res_forward_subsumed:                   0
% 3.49/0.99  res_backward_subsumed:                  0
% 3.49/0.99  res_forward_subsumption_resolution:     0
% 3.49/0.99  res_backward_subsumption_resolution:    0
% 3.49/0.99  res_clause_to_clause_subsumption:       4242
% 3.49/0.99  res_orphan_elimination:                 0
% 3.49/0.99  res_tautology_del:                      330
% 3.49/0.99  res_num_eq_res_simplified:              0
% 3.49/0.99  res_num_sel_changes:                    0
% 3.49/0.99  res_moves_from_active_to_pass:          0
% 3.49/0.99  
% 3.49/0.99  ------ Superposition
% 3.49/0.99  
% 3.49/0.99  sup_time_total:                         0.
% 3.49/0.99  sup_time_generating:                    0.
% 3.49/0.99  sup_time_sim_full:                      0.
% 3.49/0.99  sup_time_sim_immed:                     0.
% 3.49/0.99  
% 3.49/0.99  sup_num_of_clauses:                     567
% 3.49/0.99  sup_num_in_active:                      154
% 3.49/0.99  sup_num_in_passive:                     413
% 3.49/0.99  sup_num_of_loops:                       162
% 3.49/0.99  sup_fw_superposition:                   371
% 3.49/0.99  sup_bw_superposition:                   340
% 3.49/0.99  sup_immediate_simplified:               82
% 3.49/0.99  sup_given_eliminated:                   0
% 3.49/0.99  comparisons_done:                       0
% 3.49/0.99  comparisons_avoided:                    0
% 3.49/0.99  
% 3.49/0.99  ------ Simplifications
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  sim_fw_subset_subsumed:                 49
% 3.49/0.99  sim_bw_subset_subsumed:                 6
% 3.49/0.99  sim_fw_subsumed:                        31
% 3.49/0.99  sim_bw_subsumed:                        2
% 3.49/0.99  sim_fw_subsumption_res:                 5
% 3.49/0.99  sim_bw_subsumption_res:                 0
% 3.49/0.99  sim_tautology_del:                      3
% 3.49/0.99  sim_eq_tautology_del:                   12
% 3.49/0.99  sim_eq_res_simp:                        0
% 3.49/0.99  sim_fw_demodulated:                     4
% 3.49/0.99  sim_bw_demodulated:                     7
% 3.49/0.99  sim_light_normalised:                   7
% 3.49/0.99  sim_joinable_taut:                      0
% 3.49/0.99  sim_joinable_simp:                      0
% 3.49/0.99  sim_ac_normalised:                      0
% 3.49/0.99  sim_smt_subsumption:                    0
% 3.49/0.99  
%------------------------------------------------------------------------------
