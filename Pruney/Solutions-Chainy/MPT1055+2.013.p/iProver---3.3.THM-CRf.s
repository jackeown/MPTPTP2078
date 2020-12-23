%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:09 EST 2020

% Result     : Theorem 15.56s
% Output     : CNFRefutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 592 expanded)
%              Number of clauses        :   78 ( 160 expanded)
%              Number of leaves         :   23 ( 185 expanded)
%              Depth                    :   16
%              Number of atoms          :  497 (4411 expanded)
%              Number of equality atoms :  145 ( 225 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f72,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f66,f71,f70,f69,f68,f67])).

fof(f115,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f55])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f116,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f114,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f112,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1597,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1609,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4715,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1597,c_1609])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1613,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2830,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1597,c_1613])).

cnf(c_9773,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4715,c_2830])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X1)
    | r1_tarski(X3,k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1602,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,X3))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1598,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2569,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1623])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1627,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7707,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_1627])).

cnf(c_11617,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(sK3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,sK0))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_7707])).

cnf(c_78717,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2))) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9773,c_11617])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1608,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6012,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1597,c_1608])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1614,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3120,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1597,c_1614])).

cnf(c_12670,plain,
    ( k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6012,c_3120,c_9773])).

cnf(c_78904,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78717,c_12670])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1611,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3638,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1597,c_1611])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1600,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9099,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_1600])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1612,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4103,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1597,c_1612])).

cnf(c_14419,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9099,c_4103])).

cnf(c_19,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1617,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14426,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14419,c_1617])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_49,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_285])).

cnf(c_2227,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_11,c_42])).

cnf(c_2303,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_362,c_2227])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2444,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2303,c_15])).

cnf(c_2445,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_33754,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14426,c_49,c_2445])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1618,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1619,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6050,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1627])).

cnf(c_36006,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_6050])).

cnf(c_40291,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33754,c_36006])).

cnf(c_38,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1601,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9098,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_1601])).

cnf(c_15788,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9098,c_4103])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_9056,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9061,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9056])).

cnf(c_736,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1977,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_1979,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_50,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78904,c_40291,c_33754,c_15788,c_9061,c_2445,c_1979,c_0,c_51,c_50,c_49,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.56/2.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.56/2.52  
% 15.56/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.56/2.52  
% 15.56/2.52  ------  iProver source info
% 15.56/2.52  
% 15.56/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.56/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.56/2.52  git: non_committed_changes: false
% 15.56/2.52  git: last_make_outside_of_git: false
% 15.56/2.52  
% 15.56/2.52  ------ 
% 15.56/2.52  
% 15.56/2.52  ------ Input Options
% 15.56/2.52  
% 15.56/2.52  --out_options                           all
% 15.56/2.52  --tptp_safe_out                         true
% 15.56/2.52  --problem_path                          ""
% 15.56/2.52  --include_path                          ""
% 15.56/2.52  --clausifier                            res/vclausify_rel
% 15.56/2.52  --clausifier_options                    --mode clausify
% 15.56/2.52  --stdin                                 false
% 15.56/2.52  --stats_out                             sel
% 15.56/2.52  
% 15.56/2.52  ------ General Options
% 15.56/2.52  
% 15.56/2.52  --fof                                   false
% 15.56/2.52  --time_out_real                         604.99
% 15.56/2.52  --time_out_virtual                      -1.
% 15.56/2.52  --symbol_type_check                     false
% 15.56/2.52  --clausify_out                          false
% 15.56/2.52  --sig_cnt_out                           false
% 15.56/2.52  --trig_cnt_out                          false
% 15.56/2.52  --trig_cnt_out_tolerance                1.
% 15.56/2.52  --trig_cnt_out_sk_spl                   false
% 15.56/2.52  --abstr_cl_out                          false
% 15.56/2.52  
% 15.56/2.52  ------ Global Options
% 15.56/2.52  
% 15.56/2.52  --schedule                              none
% 15.56/2.52  --add_important_lit                     false
% 15.56/2.52  --prop_solver_per_cl                    1000
% 15.56/2.52  --min_unsat_core                        false
% 15.56/2.52  --soft_assumptions                      false
% 15.56/2.52  --soft_lemma_size                       3
% 15.56/2.52  --prop_impl_unit_size                   0
% 15.56/2.52  --prop_impl_unit                        []
% 15.56/2.52  --share_sel_clauses                     true
% 15.56/2.52  --reset_solvers                         false
% 15.56/2.52  --bc_imp_inh                            [conj_cone]
% 15.56/2.52  --conj_cone_tolerance                   3.
% 15.56/2.52  --extra_neg_conj                        none
% 15.56/2.52  --large_theory_mode                     true
% 15.56/2.52  --prolific_symb_bound                   200
% 15.56/2.52  --lt_threshold                          2000
% 15.56/2.52  --clause_weak_htbl                      true
% 15.56/2.52  --gc_record_bc_elim                     false
% 15.56/2.52  
% 15.56/2.52  ------ Preprocessing Options
% 15.56/2.52  
% 15.56/2.52  --preprocessing_flag                    true
% 15.56/2.52  --time_out_prep_mult                    0.1
% 15.56/2.52  --splitting_mode                        input
% 15.56/2.52  --splitting_grd                         true
% 15.56/2.52  --splitting_cvd                         false
% 15.56/2.52  --splitting_cvd_svl                     false
% 15.56/2.52  --splitting_nvd                         32
% 15.56/2.52  --sub_typing                            true
% 15.56/2.52  --prep_gs_sim                           false
% 15.56/2.52  --prep_unflatten                        true
% 15.56/2.52  --prep_res_sim                          true
% 15.56/2.52  --prep_upred                            true
% 15.56/2.52  --prep_sem_filter                       exhaustive
% 15.56/2.52  --prep_sem_filter_out                   false
% 15.56/2.52  --pred_elim                             false
% 15.56/2.52  --res_sim_input                         true
% 15.56/2.52  --eq_ax_congr_red                       true
% 15.56/2.52  --pure_diseq_elim                       true
% 15.56/2.52  --brand_transform                       false
% 15.56/2.52  --non_eq_to_eq                          false
% 15.56/2.52  --prep_def_merge                        true
% 15.56/2.52  --prep_def_merge_prop_impl              false
% 15.56/2.52  --prep_def_merge_mbd                    true
% 15.56/2.52  --prep_def_merge_tr_red                 false
% 15.56/2.52  --prep_def_merge_tr_cl                  false
% 15.56/2.52  --smt_preprocessing                     true
% 15.56/2.52  --smt_ac_axioms                         fast
% 15.56/2.52  --preprocessed_out                      false
% 15.56/2.52  --preprocessed_stats                    false
% 15.56/2.52  
% 15.56/2.52  ------ Abstraction refinement Options
% 15.56/2.52  
% 15.56/2.52  --abstr_ref                             []
% 15.56/2.52  --abstr_ref_prep                        false
% 15.56/2.52  --abstr_ref_until_sat                   false
% 15.56/2.52  --abstr_ref_sig_restrict                funpre
% 15.56/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.56/2.52  --abstr_ref_under                       []
% 15.56/2.52  
% 15.56/2.52  ------ SAT Options
% 15.56/2.52  
% 15.56/2.52  --sat_mode                              false
% 15.56/2.52  --sat_fm_restart_options                ""
% 15.56/2.52  --sat_gr_def                            false
% 15.56/2.52  --sat_epr_types                         true
% 15.56/2.52  --sat_non_cyclic_types                  false
% 15.56/2.52  --sat_finite_models                     false
% 15.56/2.52  --sat_fm_lemmas                         false
% 15.56/2.52  --sat_fm_prep                           false
% 15.56/2.52  --sat_fm_uc_incr                        true
% 15.56/2.52  --sat_out_model                         small
% 15.56/2.52  --sat_out_clauses                       false
% 15.56/2.52  
% 15.56/2.52  ------ QBF Options
% 15.56/2.52  
% 15.56/2.52  --qbf_mode                              false
% 15.56/2.52  --qbf_elim_univ                         false
% 15.56/2.52  --qbf_dom_inst                          none
% 15.56/2.52  --qbf_dom_pre_inst                      false
% 15.56/2.52  --qbf_sk_in                             false
% 15.56/2.52  --qbf_pred_elim                         true
% 15.56/2.52  --qbf_split                             512
% 15.56/2.52  
% 15.56/2.52  ------ BMC1 Options
% 15.56/2.52  
% 15.56/2.52  --bmc1_incremental                      false
% 15.56/2.52  --bmc1_axioms                           reachable_all
% 15.56/2.52  --bmc1_min_bound                        0
% 15.56/2.52  --bmc1_max_bound                        -1
% 15.56/2.52  --bmc1_max_bound_default                -1
% 15.56/2.52  --bmc1_symbol_reachability              true
% 15.56/2.52  --bmc1_property_lemmas                  false
% 15.56/2.52  --bmc1_k_induction                      false
% 15.56/2.52  --bmc1_non_equiv_states                 false
% 15.56/2.52  --bmc1_deadlock                         false
% 15.56/2.52  --bmc1_ucm                              false
% 15.56/2.52  --bmc1_add_unsat_core                   none
% 15.56/2.52  --bmc1_unsat_core_children              false
% 15.56/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.56/2.52  --bmc1_out_stat                         full
% 15.56/2.52  --bmc1_ground_init                      false
% 15.56/2.52  --bmc1_pre_inst_next_state              false
% 15.56/2.52  --bmc1_pre_inst_state                   false
% 15.56/2.52  --bmc1_pre_inst_reach_state             false
% 15.56/2.52  --bmc1_out_unsat_core                   false
% 15.56/2.52  --bmc1_aig_witness_out                  false
% 15.56/2.52  --bmc1_verbose                          false
% 15.56/2.52  --bmc1_dump_clauses_tptp                false
% 15.56/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.56/2.52  --bmc1_dump_file                        -
% 15.56/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.56/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.56/2.52  --bmc1_ucm_extend_mode                  1
% 15.56/2.52  --bmc1_ucm_init_mode                    2
% 15.56/2.52  --bmc1_ucm_cone_mode                    none
% 15.56/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.56/2.52  --bmc1_ucm_relax_model                  4
% 15.56/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.56/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.56/2.52  --bmc1_ucm_layered_model                none
% 15.56/2.52  --bmc1_ucm_max_lemma_size               10
% 15.56/2.52  
% 15.56/2.52  ------ AIG Options
% 15.56/2.52  
% 15.56/2.52  --aig_mode                              false
% 15.56/2.52  
% 15.56/2.52  ------ Instantiation Options
% 15.56/2.52  
% 15.56/2.52  --instantiation_flag                    true
% 15.56/2.52  --inst_sos_flag                         false
% 15.56/2.52  --inst_sos_phase                        true
% 15.56/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.56/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.56/2.52  --inst_lit_sel_side                     num_symb
% 15.56/2.52  --inst_solver_per_active                1400
% 15.56/2.52  --inst_solver_calls_frac                1.
% 15.56/2.52  --inst_passive_queue_type               priority_queues
% 15.56/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.56/2.52  --inst_passive_queues_freq              [25;2]
% 15.56/2.52  --inst_dismatching                      true
% 15.56/2.52  --inst_eager_unprocessed_to_passive     true
% 15.56/2.52  --inst_prop_sim_given                   true
% 15.56/2.52  --inst_prop_sim_new                     false
% 15.56/2.52  --inst_subs_new                         false
% 15.56/2.52  --inst_eq_res_simp                      false
% 15.56/2.52  --inst_subs_given                       false
% 15.56/2.52  --inst_orphan_elimination               true
% 15.56/2.52  --inst_learning_loop_flag               true
% 15.56/2.52  --inst_learning_start                   3000
% 15.56/2.52  --inst_learning_factor                  2
% 15.56/2.52  --inst_start_prop_sim_after_learn       3
% 15.56/2.52  --inst_sel_renew                        solver
% 15.56/2.52  --inst_lit_activity_flag                true
% 15.56/2.52  --inst_restr_to_given                   false
% 15.56/2.52  --inst_activity_threshold               500
% 15.56/2.52  --inst_out_proof                        true
% 15.56/2.52  
% 15.56/2.52  ------ Resolution Options
% 15.56/2.52  
% 15.56/2.52  --resolution_flag                       true
% 15.56/2.52  --res_lit_sel                           adaptive
% 15.56/2.52  --res_lit_sel_side                      none
% 15.56/2.52  --res_ordering                          kbo
% 15.56/2.52  --res_to_prop_solver                    active
% 15.56/2.52  --res_prop_simpl_new                    false
% 15.56/2.52  --res_prop_simpl_given                  true
% 15.56/2.52  --res_passive_queue_type                priority_queues
% 15.56/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.56/2.52  --res_passive_queues_freq               [15;5]
% 15.56/2.52  --res_forward_subs                      full
% 15.56/2.52  --res_backward_subs                     full
% 15.56/2.52  --res_forward_subs_resolution           true
% 15.56/2.52  --res_backward_subs_resolution          true
% 15.56/2.52  --res_orphan_elimination                true
% 15.56/2.52  --res_time_limit                        2.
% 15.56/2.52  --res_out_proof                         true
% 15.56/2.52  
% 15.56/2.52  ------ Superposition Options
% 15.56/2.52  
% 15.56/2.52  --superposition_flag                    true
% 15.56/2.52  --sup_passive_queue_type                priority_queues
% 15.56/2.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.56/2.52  --sup_passive_queues_freq               [1;4]
% 15.56/2.52  --demod_completeness_check              fast
% 15.56/2.52  --demod_use_ground                      true
% 15.56/2.52  --sup_to_prop_solver                    passive
% 15.56/2.52  --sup_prop_simpl_new                    true
% 15.56/2.52  --sup_prop_simpl_given                  true
% 15.56/2.52  --sup_fun_splitting                     false
% 15.56/2.52  --sup_smt_interval                      50000
% 15.56/2.52  
% 15.56/2.52  ------ Superposition Simplification Setup
% 15.56/2.52  
% 15.56/2.52  --sup_indices_passive                   []
% 15.56/2.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.56/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_full_bw                           [BwDemod]
% 15.56/2.52  --sup_immed_triv                        [TrivRules]
% 15.56/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.56/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_immed_bw_main                     []
% 15.56/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.56/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.56/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.56/2.52  
% 15.56/2.52  ------ Combination Options
% 15.56/2.52  
% 15.56/2.52  --comb_res_mult                         3
% 15.56/2.52  --comb_sup_mult                         2
% 15.56/2.52  --comb_inst_mult                        10
% 15.56/2.52  
% 15.56/2.52  ------ Debug Options
% 15.56/2.52  
% 15.56/2.52  --dbg_backtrace                         false
% 15.56/2.52  --dbg_dump_prop_clauses                 false
% 15.56/2.52  --dbg_dump_prop_clauses_file            -
% 15.56/2.52  --dbg_out_stat                          false
% 15.56/2.52  ------ Parsing...
% 15.56/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.56/2.52  
% 15.56/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.56/2.52  
% 15.56/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.56/2.52  
% 15.56/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.52  ------ Proving...
% 15.56/2.52  ------ Problem Properties 
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  clauses                                 43
% 15.56/2.52  conjectures                             9
% 15.56/2.52  EPR                                     10
% 15.56/2.52  Horn                                    39
% 15.56/2.52  unary                                   14
% 15.56/2.52  binary                                  13
% 15.56/2.52  lits                                    100
% 15.56/2.52  lits eq                                 15
% 15.56/2.52  fd_pure                                 0
% 15.56/2.52  fd_pseudo                               0
% 15.56/2.52  fd_cond                                 2
% 15.56/2.52  fd_pseudo_cond                          1
% 15.56/2.52  AC symbols                              0
% 15.56/2.52  
% 15.56/2.52  ------ Input Options Time Limit: Unbounded
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  ------ 
% 15.56/2.52  Current options:
% 15.56/2.52  ------ 
% 15.56/2.52  
% 15.56/2.52  ------ Input Options
% 15.56/2.52  
% 15.56/2.52  --out_options                           all
% 15.56/2.52  --tptp_safe_out                         true
% 15.56/2.52  --problem_path                          ""
% 15.56/2.52  --include_path                          ""
% 15.56/2.52  --clausifier                            res/vclausify_rel
% 15.56/2.52  --clausifier_options                    --mode clausify
% 15.56/2.52  --stdin                                 false
% 15.56/2.52  --stats_out                             sel
% 15.56/2.52  
% 15.56/2.52  ------ General Options
% 15.56/2.52  
% 15.56/2.52  --fof                                   false
% 15.56/2.52  --time_out_real                         604.99
% 15.56/2.52  --time_out_virtual                      -1.
% 15.56/2.52  --symbol_type_check                     false
% 15.56/2.52  --clausify_out                          false
% 15.56/2.52  --sig_cnt_out                           false
% 15.56/2.52  --trig_cnt_out                          false
% 15.56/2.52  --trig_cnt_out_tolerance                1.
% 15.56/2.52  --trig_cnt_out_sk_spl                   false
% 15.56/2.52  --abstr_cl_out                          false
% 15.56/2.52  
% 15.56/2.52  ------ Global Options
% 15.56/2.52  
% 15.56/2.52  --schedule                              none
% 15.56/2.52  --add_important_lit                     false
% 15.56/2.52  --prop_solver_per_cl                    1000
% 15.56/2.52  --min_unsat_core                        false
% 15.56/2.52  --soft_assumptions                      false
% 15.56/2.52  --soft_lemma_size                       3
% 15.56/2.52  --prop_impl_unit_size                   0
% 15.56/2.52  --prop_impl_unit                        []
% 15.56/2.52  --share_sel_clauses                     true
% 15.56/2.52  --reset_solvers                         false
% 15.56/2.52  --bc_imp_inh                            [conj_cone]
% 15.56/2.52  --conj_cone_tolerance                   3.
% 15.56/2.52  --extra_neg_conj                        none
% 15.56/2.52  --large_theory_mode                     true
% 15.56/2.52  --prolific_symb_bound                   200
% 15.56/2.52  --lt_threshold                          2000
% 15.56/2.52  --clause_weak_htbl                      true
% 15.56/2.52  --gc_record_bc_elim                     false
% 15.56/2.52  
% 15.56/2.52  ------ Preprocessing Options
% 15.56/2.52  
% 15.56/2.52  --preprocessing_flag                    true
% 15.56/2.52  --time_out_prep_mult                    0.1
% 15.56/2.52  --splitting_mode                        input
% 15.56/2.52  --splitting_grd                         true
% 15.56/2.52  --splitting_cvd                         false
% 15.56/2.52  --splitting_cvd_svl                     false
% 15.56/2.52  --splitting_nvd                         32
% 15.56/2.52  --sub_typing                            true
% 15.56/2.52  --prep_gs_sim                           false
% 15.56/2.52  --prep_unflatten                        true
% 15.56/2.52  --prep_res_sim                          true
% 15.56/2.52  --prep_upred                            true
% 15.56/2.52  --prep_sem_filter                       exhaustive
% 15.56/2.52  --prep_sem_filter_out                   false
% 15.56/2.52  --pred_elim                             false
% 15.56/2.52  --res_sim_input                         true
% 15.56/2.52  --eq_ax_congr_red                       true
% 15.56/2.52  --pure_diseq_elim                       true
% 15.56/2.52  --brand_transform                       false
% 15.56/2.52  --non_eq_to_eq                          false
% 15.56/2.52  --prep_def_merge                        true
% 15.56/2.52  --prep_def_merge_prop_impl              false
% 15.56/2.52  --prep_def_merge_mbd                    true
% 15.56/2.52  --prep_def_merge_tr_red                 false
% 15.56/2.52  --prep_def_merge_tr_cl                  false
% 15.56/2.52  --smt_preprocessing                     true
% 15.56/2.52  --smt_ac_axioms                         fast
% 15.56/2.52  --preprocessed_out                      false
% 15.56/2.52  --preprocessed_stats                    false
% 15.56/2.52  
% 15.56/2.52  ------ Abstraction refinement Options
% 15.56/2.52  
% 15.56/2.52  --abstr_ref                             []
% 15.56/2.52  --abstr_ref_prep                        false
% 15.56/2.52  --abstr_ref_until_sat                   false
% 15.56/2.52  --abstr_ref_sig_restrict                funpre
% 15.56/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.56/2.52  --abstr_ref_under                       []
% 15.56/2.52  
% 15.56/2.52  ------ SAT Options
% 15.56/2.52  
% 15.56/2.52  --sat_mode                              false
% 15.56/2.52  --sat_fm_restart_options                ""
% 15.56/2.52  --sat_gr_def                            false
% 15.56/2.52  --sat_epr_types                         true
% 15.56/2.52  --sat_non_cyclic_types                  false
% 15.56/2.52  --sat_finite_models                     false
% 15.56/2.52  --sat_fm_lemmas                         false
% 15.56/2.52  --sat_fm_prep                           false
% 15.56/2.52  --sat_fm_uc_incr                        true
% 15.56/2.52  --sat_out_model                         small
% 15.56/2.52  --sat_out_clauses                       false
% 15.56/2.52  
% 15.56/2.52  ------ QBF Options
% 15.56/2.52  
% 15.56/2.52  --qbf_mode                              false
% 15.56/2.52  --qbf_elim_univ                         false
% 15.56/2.52  --qbf_dom_inst                          none
% 15.56/2.52  --qbf_dom_pre_inst                      false
% 15.56/2.52  --qbf_sk_in                             false
% 15.56/2.52  --qbf_pred_elim                         true
% 15.56/2.52  --qbf_split                             512
% 15.56/2.52  
% 15.56/2.52  ------ BMC1 Options
% 15.56/2.52  
% 15.56/2.52  --bmc1_incremental                      false
% 15.56/2.52  --bmc1_axioms                           reachable_all
% 15.56/2.52  --bmc1_min_bound                        0
% 15.56/2.52  --bmc1_max_bound                        -1
% 15.56/2.52  --bmc1_max_bound_default                -1
% 15.56/2.52  --bmc1_symbol_reachability              true
% 15.56/2.52  --bmc1_property_lemmas                  false
% 15.56/2.52  --bmc1_k_induction                      false
% 15.56/2.52  --bmc1_non_equiv_states                 false
% 15.56/2.52  --bmc1_deadlock                         false
% 15.56/2.52  --bmc1_ucm                              false
% 15.56/2.52  --bmc1_add_unsat_core                   none
% 15.56/2.52  --bmc1_unsat_core_children              false
% 15.56/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.56/2.52  --bmc1_out_stat                         full
% 15.56/2.52  --bmc1_ground_init                      false
% 15.56/2.52  --bmc1_pre_inst_next_state              false
% 15.56/2.52  --bmc1_pre_inst_state                   false
% 15.56/2.52  --bmc1_pre_inst_reach_state             false
% 15.56/2.52  --bmc1_out_unsat_core                   false
% 15.56/2.52  --bmc1_aig_witness_out                  false
% 15.56/2.52  --bmc1_verbose                          false
% 15.56/2.52  --bmc1_dump_clauses_tptp                false
% 15.56/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.56/2.52  --bmc1_dump_file                        -
% 15.56/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.56/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.56/2.52  --bmc1_ucm_extend_mode                  1
% 15.56/2.52  --bmc1_ucm_init_mode                    2
% 15.56/2.52  --bmc1_ucm_cone_mode                    none
% 15.56/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.56/2.52  --bmc1_ucm_relax_model                  4
% 15.56/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.56/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.56/2.52  --bmc1_ucm_layered_model                none
% 15.56/2.52  --bmc1_ucm_max_lemma_size               10
% 15.56/2.52  
% 15.56/2.52  ------ AIG Options
% 15.56/2.52  
% 15.56/2.52  --aig_mode                              false
% 15.56/2.52  
% 15.56/2.52  ------ Instantiation Options
% 15.56/2.52  
% 15.56/2.52  --instantiation_flag                    true
% 15.56/2.52  --inst_sos_flag                         false
% 15.56/2.52  --inst_sos_phase                        true
% 15.56/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.56/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.56/2.52  --inst_lit_sel_side                     num_symb
% 15.56/2.52  --inst_solver_per_active                1400
% 15.56/2.52  --inst_solver_calls_frac                1.
% 15.56/2.52  --inst_passive_queue_type               priority_queues
% 15.56/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.56/2.52  --inst_passive_queues_freq              [25;2]
% 15.56/2.52  --inst_dismatching                      true
% 15.56/2.52  --inst_eager_unprocessed_to_passive     true
% 15.56/2.52  --inst_prop_sim_given                   true
% 15.56/2.52  --inst_prop_sim_new                     false
% 15.56/2.52  --inst_subs_new                         false
% 15.56/2.52  --inst_eq_res_simp                      false
% 15.56/2.52  --inst_subs_given                       false
% 15.56/2.52  --inst_orphan_elimination               true
% 15.56/2.52  --inst_learning_loop_flag               true
% 15.56/2.52  --inst_learning_start                   3000
% 15.56/2.52  --inst_learning_factor                  2
% 15.56/2.52  --inst_start_prop_sim_after_learn       3
% 15.56/2.52  --inst_sel_renew                        solver
% 15.56/2.52  --inst_lit_activity_flag                true
% 15.56/2.52  --inst_restr_to_given                   false
% 15.56/2.52  --inst_activity_threshold               500
% 15.56/2.52  --inst_out_proof                        true
% 15.56/2.52  
% 15.56/2.52  ------ Resolution Options
% 15.56/2.52  
% 15.56/2.52  --resolution_flag                       true
% 15.56/2.52  --res_lit_sel                           adaptive
% 15.56/2.52  --res_lit_sel_side                      none
% 15.56/2.52  --res_ordering                          kbo
% 15.56/2.52  --res_to_prop_solver                    active
% 15.56/2.52  --res_prop_simpl_new                    false
% 15.56/2.52  --res_prop_simpl_given                  true
% 15.56/2.52  --res_passive_queue_type                priority_queues
% 15.56/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.56/2.52  --res_passive_queues_freq               [15;5]
% 15.56/2.52  --res_forward_subs                      full
% 15.56/2.52  --res_backward_subs                     full
% 15.56/2.52  --res_forward_subs_resolution           true
% 15.56/2.52  --res_backward_subs_resolution          true
% 15.56/2.52  --res_orphan_elimination                true
% 15.56/2.52  --res_time_limit                        2.
% 15.56/2.52  --res_out_proof                         true
% 15.56/2.52  
% 15.56/2.52  ------ Superposition Options
% 15.56/2.52  
% 15.56/2.52  --superposition_flag                    true
% 15.56/2.52  --sup_passive_queue_type                priority_queues
% 15.56/2.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.56/2.52  --sup_passive_queues_freq               [1;4]
% 15.56/2.52  --demod_completeness_check              fast
% 15.56/2.52  --demod_use_ground                      true
% 15.56/2.52  --sup_to_prop_solver                    passive
% 15.56/2.52  --sup_prop_simpl_new                    true
% 15.56/2.52  --sup_prop_simpl_given                  true
% 15.56/2.52  --sup_fun_splitting                     false
% 15.56/2.52  --sup_smt_interval                      50000
% 15.56/2.52  
% 15.56/2.52  ------ Superposition Simplification Setup
% 15.56/2.52  
% 15.56/2.52  --sup_indices_passive                   []
% 15.56/2.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.56/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.56/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_full_bw                           [BwDemod]
% 15.56/2.52  --sup_immed_triv                        [TrivRules]
% 15.56/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.56/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_immed_bw_main                     []
% 15.56/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.56/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.56/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.56/2.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.56/2.52  
% 15.56/2.52  ------ Combination Options
% 15.56/2.52  
% 15.56/2.52  --comb_res_mult                         3
% 15.56/2.52  --comb_sup_mult                         2
% 15.56/2.52  --comb_inst_mult                        10
% 15.56/2.52  
% 15.56/2.52  ------ Debug Options
% 15.56/2.52  
% 15.56/2.52  --dbg_backtrace                         false
% 15.56/2.52  --dbg_dump_prop_clauses                 false
% 15.56/2.52  --dbg_dump_prop_clauses_file            -
% 15.56/2.52  --dbg_out_stat                          false
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  ------ Proving...
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  % SZS status Theorem for theBenchmark.p
% 15.56/2.52  
% 15.56/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.56/2.52  
% 15.56/2.52  fof(f27,conjecture,(
% 15.56/2.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f28,negated_conjecture,(
% 15.56/2.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 15.56/2.52    inference(negated_conjecture,[],[f27])).
% 15.56/2.52  
% 15.56/2.52  fof(f57,plain,(
% 15.56/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.56/2.52    inference(ennf_transformation,[],[f28])).
% 15.56/2.52  
% 15.56/2.52  fof(f58,plain,(
% 15.56/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.56/2.52    inference(flattening,[],[f57])).
% 15.56/2.52  
% 15.56/2.52  fof(f65,plain,(
% 15.56/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.56/2.52    inference(nnf_transformation,[],[f58])).
% 15.56/2.52  
% 15.56/2.52  fof(f66,plain,(
% 15.56/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.56/2.52    inference(flattening,[],[f65])).
% 15.56/2.52  
% 15.56/2.52  fof(f71,plain,(
% 15.56/2.52    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 15.56/2.52    introduced(choice_axiom,[])).
% 15.56/2.52  
% 15.56/2.52  fof(f70,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 15.56/2.52    introduced(choice_axiom,[])).
% 15.56/2.52  
% 15.56/2.52  fof(f69,plain,(
% 15.56/2.52    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 15.56/2.52    introduced(choice_axiom,[])).
% 15.56/2.52  
% 15.56/2.52  fof(f68,plain,(
% 15.56/2.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 15.56/2.52    introduced(choice_axiom,[])).
% 15.56/2.52  
% 15.56/2.52  fof(f67,plain,(
% 15.56/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 15.56/2.52    introduced(choice_axiom,[])).
% 15.56/2.52  
% 15.56/2.52  fof(f72,plain,(
% 15.56/2.52    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 15.56/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f66,f71,f70,f69,f68,f67])).
% 15.56/2.52  
% 15.56/2.52  fof(f115,plain,(
% 15.56/2.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f22,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f49,plain,(
% 15.56/2.52    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.56/2.52    inference(ennf_transformation,[],[f22])).
% 15.56/2.52  
% 15.56/2.52  fof(f99,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f49])).
% 15.56/2.52  
% 15.56/2.52  fof(f19,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f46,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.56/2.52    inference(ennf_transformation,[],[f19])).
% 15.56/2.52  
% 15.56/2.52  fof(f96,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f46])).
% 15.56/2.52  
% 15.56/2.52  fof(f26,axiom,(
% 15.56/2.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f55,plain,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.56/2.52    inference(ennf_transformation,[],[f26])).
% 15.56/2.52  
% 15.56/2.52  fof(f56,plain,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.56/2.52    inference(flattening,[],[f55])).
% 15.56/2.52  
% 15.56/2.52  fof(f109,plain,(
% 15.56/2.52    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f56])).
% 15.56/2.52  
% 15.56/2.52  fof(f116,plain,(
% 15.56/2.52    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f7,axiom,(
% 15.56/2.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f63,plain,(
% 15.56/2.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.56/2.52    inference(nnf_transformation,[],[f7])).
% 15.56/2.52  
% 15.56/2.52  fof(f83,plain,(
% 15.56/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f63])).
% 15.56/2.52  
% 15.56/2.52  fof(f3,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f31,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.56/2.52    inference(ennf_transformation,[],[f3])).
% 15.56/2.52  
% 15.56/2.52  fof(f32,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.56/2.52    inference(flattening,[],[f31])).
% 15.56/2.52  
% 15.56/2.52  fof(f77,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f32])).
% 15.56/2.52  
% 15.56/2.52  fof(f23,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f50,plain,(
% 15.56/2.52    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 15.56/2.52    inference(ennf_transformation,[],[f23])).
% 15.56/2.52  
% 15.56/2.52  fof(f102,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f50])).
% 15.56/2.52  
% 15.56/2.52  fof(f18,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f45,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.56/2.52    inference(ennf_transformation,[],[f18])).
% 15.56/2.52  
% 15.56/2.52  fof(f95,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f45])).
% 15.56/2.52  
% 15.56/2.52  fof(f21,axiom,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f48,plain,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.56/2.52    inference(ennf_transformation,[],[f21])).
% 15.56/2.52  
% 15.56/2.52  fof(f98,plain,(
% 15.56/2.52    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f48])).
% 15.56/2.52  
% 15.56/2.52  fof(f118,plain,(
% 15.56/2.52    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f20,axiom,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f47,plain,(
% 15.56/2.52    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.56/2.52    inference(ennf_transformation,[],[f20])).
% 15.56/2.52  
% 15.56/2.52  fof(f97,plain,(
% 15.56/2.52    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f47])).
% 15.56/2.52  
% 15.56/2.52  fof(f15,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f41,plain,(
% 15.56/2.52    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.56/2.52    inference(ennf_transformation,[],[f15])).
% 15.56/2.52  
% 15.56/2.52  fof(f42,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.56/2.52    inference(flattening,[],[f41])).
% 15.56/2.52  
% 15.56/2.52  fof(f92,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f42])).
% 15.56/2.52  
% 15.56/2.52  fof(f113,plain,(
% 15.56/2.52    v1_funct_1(sK2)),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f9,axiom,(
% 15.56/2.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f33,plain,(
% 15.56/2.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.56/2.52    inference(ennf_transformation,[],[f9])).
% 15.56/2.52  
% 15.56/2.52  fof(f85,plain,(
% 15.56/2.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f33])).
% 15.56/2.52  
% 15.56/2.52  fof(f84,plain,(
% 15.56/2.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f63])).
% 15.56/2.52  
% 15.56/2.52  fof(f11,axiom,(
% 15.56/2.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f88,plain,(
% 15.56/2.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.56/2.52    inference(cnf_transformation,[],[f11])).
% 15.56/2.52  
% 15.56/2.52  fof(f14,axiom,(
% 15.56/2.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f39,plain,(
% 15.56/2.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.56/2.52    inference(ennf_transformation,[],[f14])).
% 15.56/2.52  
% 15.56/2.52  fof(f40,plain,(
% 15.56/2.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.56/2.52    inference(flattening,[],[f39])).
% 15.56/2.52  
% 15.56/2.52  fof(f91,plain,(
% 15.56/2.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f40])).
% 15.56/2.52  
% 15.56/2.52  fof(f12,axiom,(
% 15.56/2.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f35,plain,(
% 15.56/2.52    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 15.56/2.52    inference(ennf_transformation,[],[f12])).
% 15.56/2.52  
% 15.56/2.52  fof(f36,plain,(
% 15.56/2.52    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 15.56/2.52    inference(flattening,[],[f35])).
% 15.56/2.52  
% 15.56/2.52  fof(f89,plain,(
% 15.56/2.52    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 15.56/2.52    inference(cnf_transformation,[],[f36])).
% 15.56/2.52  
% 15.56/2.52  fof(f119,plain,(
% 15.56/2.52    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f2,axiom,(
% 15.56/2.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f59,plain,(
% 15.56/2.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.56/2.52    inference(nnf_transformation,[],[f2])).
% 15.56/2.52  
% 15.56/2.52  fof(f60,plain,(
% 15.56/2.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.56/2.52    inference(flattening,[],[f59])).
% 15.56/2.52  
% 15.56/2.52  fof(f74,plain,(
% 15.56/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.56/2.52    inference(cnf_transformation,[],[f60])).
% 15.56/2.52  
% 15.56/2.52  fof(f121,plain,(
% 15.56/2.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.56/2.52    inference(equality_resolution,[],[f74])).
% 15.56/2.52  
% 15.56/2.52  fof(f1,axiom,(
% 15.56/2.52    v1_xboole_0(k1_xboole_0)),
% 15.56/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.56/2.52  
% 15.56/2.52  fof(f73,plain,(
% 15.56/2.52    v1_xboole_0(k1_xboole_0)),
% 15.56/2.52    inference(cnf_transformation,[],[f1])).
% 15.56/2.52  
% 15.56/2.52  fof(f114,plain,(
% 15.56/2.52    v1_funct_2(sK2,sK0,sK1)),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  fof(f112,plain,(
% 15.56/2.52    ~v1_xboole_0(sK1)),
% 15.56/2.52    inference(cnf_transformation,[],[f72])).
% 15.56/2.52  
% 15.56/2.52  cnf(c_42,negated_conjecture,
% 15.56/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.56/2.52      inference(cnf_transformation,[],[f115]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1597,plain,
% 15.56/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_27,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f99]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1609,plain,
% 15.56/2.52      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_4715,plain,
% 15.56/2.52      ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relset_1(sK0,sK1,sK2) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1609]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_23,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f96]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1613,plain,
% 15.56/2.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2830,plain,
% 15.56/2.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1613]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_9773,plain,
% 15.56/2.52      ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relat_1(sK2) ),
% 15.56/2.52      inference(light_normalisation,[status(thm)],[c_4715,c_2830]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_37,plain,
% 15.56/2.52      ( ~ v1_funct_2(X0,X1,X2)
% 15.56/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | ~ r1_tarski(X3,X1)
% 15.56/2.52      | r1_tarski(X3,k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X3)))
% 15.56/2.52      | ~ v1_funct_1(X0)
% 15.56/2.52      | k1_xboole_0 = X2 ),
% 15.56/2.52      inference(cnf_transformation,[],[f109]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1602,plain,
% 15.56/2.52      ( k1_xboole_0 = X0
% 15.56/2.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 15.56/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.56/2.52      | r1_tarski(X3,X2) != iProver_top
% 15.56/2.52      | r1_tarski(X3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,X3))) = iProver_top
% 15.56/2.52      | v1_funct_1(X1) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_41,negated_conjecture,
% 15.56/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 15.56/2.52      inference(cnf_transformation,[],[f116]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1598,plain,
% 15.56/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_11,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.56/2.52      inference(cnf_transformation,[],[f83]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1623,plain,
% 15.56/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.56/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2569,plain,
% 15.56/2.52      ( r1_tarski(sK3,sK0) = iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1598,c_1623]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_4,plain,
% 15.56/2.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 15.56/2.52      inference(cnf_transformation,[],[f77]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1627,plain,
% 15.56/2.52      ( r1_tarski(X0,X1) != iProver_top
% 15.56/2.52      | r1_tarski(X1,X2) != iProver_top
% 15.56/2.52      | r1_tarski(X0,X2) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_7707,plain,
% 15.56/2.52      ( r1_tarski(sK0,X0) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,X0) = iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_2569,c_1627]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_11617,plain,
% 15.56/2.52      ( k1_xboole_0 = X0
% 15.56/2.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 15.56/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.56/2.52      | r1_tarski(sK0,X2) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,sK0))) = iProver_top
% 15.56/2.52      | v1_funct_1(X1) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1602,c_7707]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_78717,plain,
% 15.56/2.52      ( sK1 = k1_xboole_0
% 15.56/2.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.56/2.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.56/2.52      | r1_tarski(sK0,sK0) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2))) = iProver_top
% 15.56/2.52      | v1_funct_1(sK2) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_9773,c_11617]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_28,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f102]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1608,plain,
% 15.56/2.52      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_6012,plain,
% 15.56/2.52      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1608]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_22,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f95]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1614,plain,
% 15.56/2.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_3120,plain,
% 15.56/2.52      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1614]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_12670,plain,
% 15.56/2.52      ( k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 15.56/2.52      inference(light_normalisation,[status(thm)],[c_6012,c_3120,c_9773]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_78904,plain,
% 15.56/2.52      ( sK1 = k1_xboole_0
% 15.56/2.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.56/2.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.56/2.52      | r1_tarski(sK0,sK0) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top
% 15.56/2.52      | v1_funct_1(sK2) != iProver_top ),
% 15.56/2.52      inference(light_normalisation,[status(thm)],[c_78717,c_12670]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_25,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 15.56/2.52      inference(cnf_transformation,[],[f98]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1611,plain,
% 15.56/2.52      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_3638,plain,
% 15.56/2.52      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1611]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_39,negated_conjecture,
% 15.56/2.52      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 15.56/2.52      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 15.56/2.52      inference(cnf_transformation,[],[f118]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1600,plain,
% 15.56/2.52      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_9099,plain,
% 15.56/2.52      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 15.56/2.52      inference(demodulation,[status(thm)],[c_3638,c_1600]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_24,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.56/2.52      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 15.56/2.52      inference(cnf_transformation,[],[f97]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1612,plain,
% 15.56/2.52      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 15.56/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_4103,plain,
% 15.56/2.52      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1597,c_1612]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_14419,plain,
% 15.56/2.52      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 15.56/2.52      inference(demodulation,[status(thm)],[c_9099,c_4103]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_19,plain,
% 15.56/2.52      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 15.56/2.52      | ~ r1_tarski(X0,k1_relat_1(X1))
% 15.56/2.52      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 15.56/2.52      | ~ v1_funct_1(X1)
% 15.56/2.52      | ~ v1_relat_1(X1) ),
% 15.56/2.52      inference(cnf_transformation,[],[f92]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1617,plain,
% 15.56/2.52      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 15.56/2.52      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 15.56/2.52      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 15.56/2.52      | v1_funct_1(X1) != iProver_top
% 15.56/2.52      | v1_relat_1(X1) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_14426,plain,
% 15.56/2.52      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
% 15.56/2.52      | v1_funct_1(sK2) != iProver_top
% 15.56/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_14419,c_1617]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_44,negated_conjecture,
% 15.56/2.52      ( v1_funct_1(sK2) ),
% 15.56/2.52      inference(cnf_transformation,[],[f113]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_49,plain,
% 15.56/2.52      ( v1_funct_1(sK2) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_12,plain,
% 15.56/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.56/2.52      | ~ v1_relat_1(X1)
% 15.56/2.52      | v1_relat_1(X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f85]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_10,plain,
% 15.56/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.56/2.52      inference(cnf_transformation,[],[f84]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_284,plain,
% 15.56/2.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.56/2.52      inference(prop_impl,[status(thm)],[c_10]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_285,plain,
% 15.56/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.56/2.52      inference(renaming,[status(thm)],[c_284]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_362,plain,
% 15.56/2.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.56/2.52      inference(bin_hyper_res,[status(thm)],[c_12,c_285]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2227,plain,
% 15.56/2.52      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 15.56/2.52      inference(resolution,[status(thm)],[c_11,c_42]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2303,plain,
% 15.56/2.52      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 15.56/2.52      inference(resolution,[status(thm)],[c_362,c_2227]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_15,plain,
% 15.56/2.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.56/2.52      inference(cnf_transformation,[],[f88]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2444,plain,
% 15.56/2.52      ( v1_relat_1(sK2) ),
% 15.56/2.52      inference(forward_subsumption_resolution,
% 15.56/2.52                [status(thm)],
% 15.56/2.52                [c_2303,c_15]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_2445,plain,
% 15.56/2.52      ( v1_relat_1(sK2) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_33754,plain,
% 15.56/2.52      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
% 15.56/2.52      inference(global_propositional_subsumption,
% 15.56/2.52                [status(thm)],
% 15.56/2.52                [c_14426,c_49,c_2445]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_18,plain,
% 15.56/2.52      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 15.56/2.52      | ~ v1_funct_1(X0)
% 15.56/2.52      | ~ v1_relat_1(X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f91]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1618,plain,
% 15.56/2.52      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 15.56/2.52      | v1_funct_1(X0) != iProver_top
% 15.56/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_16,plain,
% 15.56/2.52      ( ~ r1_tarski(X0,X1)
% 15.56/2.52      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 15.56/2.52      | ~ v1_relat_1(X2) ),
% 15.56/2.52      inference(cnf_transformation,[],[f89]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1619,plain,
% 15.56/2.52      ( r1_tarski(X0,X1) != iProver_top
% 15.56/2.52      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 15.56/2.52      | v1_relat_1(X2) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_6050,plain,
% 15.56/2.52      ( r1_tarski(X0,X1) != iProver_top
% 15.56/2.52      | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
% 15.56/2.52      | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
% 15.56/2.52      | v1_relat_1(X2) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1619,c_1627]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_36006,plain,
% 15.56/2.52      ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
% 15.56/2.52      | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
% 15.56/2.52      | v1_funct_1(X1) != iProver_top
% 15.56/2.52      | v1_relat_1(X1) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_1618,c_6050]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_40291,plain,
% 15.56/2.52      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 15.56/2.52      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
% 15.56/2.52      | v1_funct_1(sK2) != iProver_top
% 15.56/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.56/2.52      inference(superposition,[status(thm)],[c_33754,c_36006]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_38,negated_conjecture,
% 15.56/2.52      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 15.56/2.52      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 15.56/2.52      inference(cnf_transformation,[],[f119]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1601,plain,
% 15.56/2.52      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_9098,plain,
% 15.56/2.52      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 15.56/2.52      inference(demodulation,[status(thm)],[c_3638,c_1601]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_15788,plain,
% 15.56/2.52      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 15.56/2.52      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 15.56/2.52      inference(demodulation,[status(thm)],[c_9098,c_4103]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_3,plain,
% 15.56/2.52      ( r1_tarski(X0,X0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f121]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_9056,plain,
% 15.56/2.52      ( r1_tarski(sK0,sK0) ),
% 15.56/2.52      inference(instantiation,[status(thm)],[c_3]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_9061,plain,
% 15.56/2.52      ( r1_tarski(sK0,sK0) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_9056]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_736,plain,
% 15.56/2.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.56/2.52      theory(equality) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1977,plain,
% 15.56/2.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 15.56/2.52      inference(instantiation,[status(thm)],[c_736]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_1979,plain,
% 15.56/2.52      ( v1_xboole_0(sK1)
% 15.56/2.52      | ~ v1_xboole_0(k1_xboole_0)
% 15.56/2.52      | sK1 != k1_xboole_0 ),
% 15.56/2.52      inference(instantiation,[status(thm)],[c_1977]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_0,plain,
% 15.56/2.52      ( v1_xboole_0(k1_xboole_0) ),
% 15.56/2.52      inference(cnf_transformation,[],[f73]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_51,plain,
% 15.56/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_43,negated_conjecture,
% 15.56/2.52      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.56/2.52      inference(cnf_transformation,[],[f114]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_50,plain,
% 15.56/2.52      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.56/2.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(c_45,negated_conjecture,
% 15.56/2.52      ( ~ v1_xboole_0(sK1) ),
% 15.56/2.52      inference(cnf_transformation,[],[f112]) ).
% 15.56/2.52  
% 15.56/2.52  cnf(contradiction,plain,
% 15.56/2.52      ( $false ),
% 15.56/2.52      inference(minisat,
% 15.56/2.52                [status(thm)],
% 15.56/2.52                [c_78904,c_40291,c_33754,c_15788,c_9061,c_2445,c_1979,
% 15.56/2.52                 c_0,c_51,c_50,c_49,c_45]) ).
% 15.56/2.52  
% 15.56/2.52  
% 15.56/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.56/2.52  
% 15.56/2.52  ------                               Statistics
% 15.56/2.52  
% 15.56/2.52  ------ Selected
% 15.56/2.52  
% 15.56/2.52  total_time:                             1.833
% 15.56/2.52  
%------------------------------------------------------------------------------
