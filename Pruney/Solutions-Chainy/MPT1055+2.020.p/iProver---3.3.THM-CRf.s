%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:11 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 538 expanded)
%              Number of clauses        :   81 ( 149 expanded)
%              Number of leaves         :   23 ( 168 expanded)
%              Depth                    :   17
%              Number of atoms          :  516 (4121 expanded)
%              Number of equality atoms :  101 ( 172 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f45,f44,f43,f42,f41])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,
    ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2244,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK5)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3875,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
    | r1_tarski(X0,sK5)
    | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_7784,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
    | ~ r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
    | r1_tarski(k9_relat_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_3875])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2924,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4139,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,X0))
    | ~ r1_tarski(sK4,X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_7782,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
    | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4139])).

cnf(c_6514,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6516,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(sK3))
    | ~ r1_tarski(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_6514])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1930,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1935,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2573,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1930,c_1935])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1933,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3075,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2573,c_1933])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1936,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2692,plain,
    ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1930,c_1936])).

cnf(c_4048,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3075,c_2692])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_445,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_446,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1926,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_447,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2304,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_2305,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2474,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2475,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2474])).

cnf(c_2494,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_31,c_447,c_2305,c_2475])).

cnf(c_2495,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2494])).

cnf(c_4053,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_2495])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1934,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3076,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2573,c_1934])).

cnf(c_3924,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_2692])).

cnf(c_4923,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_3924])).

cnf(c_4937,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4923])).

cnf(c_4072,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5))
    | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4053])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_421,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_423,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_24,c_22])).

cnf(c_3087,plain,
    ( k10_relat_1(sK3,sK2) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_423,c_2573])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_362,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_4024,plain,
    ( k10_relat_1(sK3,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_362])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1937,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4027,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_1937])).

cnf(c_4044,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4027])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_433,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_434,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_2955,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_1374,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1399,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1377,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1388,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_920,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_921,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_920])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_371,c_921])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1078,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_975,c_21])).

cnf(c_1079,plain,
    ( r1_tarski(sK4,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_1081,plain,
    ( r1_tarski(sK4,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7784,c_7782,c_6516,c_4937,c_4072,c_4044,c_2955,c_2474,c_2304,c_1399,c_1388,c_1081,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.55/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.99  
% 3.55/0.99  ------  iProver source info
% 3.55/0.99  
% 3.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.99  git: non_committed_changes: false
% 3.55/0.99  git: last_make_outside_of_git: false
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    --mode clausify
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         false
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     num_symb
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       true
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     false
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   []
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_full_bw                           [BwDemod]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  ------ Parsing...
% 3.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.99  ------ Proving...
% 3.55/0.99  ------ Problem Properties 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  clauses                                 25
% 3.55/0.99  conjectures                             5
% 3.55/0.99  EPR                                     5
% 3.55/0.99  Horn                                    22
% 3.55/0.99  unary                                   7
% 3.55/0.99  binary                                  12
% 3.55/0.99  lits                                    50
% 3.55/0.99  lits eq                                 9
% 3.55/0.99  fd_pure                                 0
% 3.55/0.99  fd_pseudo                               0
% 3.55/0.99  fd_cond                                 0
% 3.55/0.99  fd_pseudo_cond                          2
% 3.55/0.99  AC symbols                              0
% 3.55/0.99  
% 3.55/0.99  ------ Schedule dynamic 5 is on 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  Current options:
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    --mode clausify
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         false
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     none
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       false
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     false
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   []
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_full_bw                           [BwDemod]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ Proving...
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS status Theorem for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  fof(f2,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f17,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.55/0.99    inference(ennf_transformation,[],[f2])).
% 3.55/0.99  
% 3.55/0.99  fof(f18,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.55/0.99    inference(flattening,[],[f17])).
% 3.55/0.99  
% 3.55/0.99  fof(f48,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f18])).
% 3.55/0.99  
% 3.55/0.99  fof(f8,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f22,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(ennf_transformation,[],[f8])).
% 3.55/0.99  
% 3.55/0.99  fof(f23,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(flattening,[],[f22])).
% 3.55/0.99  
% 3.55/0.99  fof(f57,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f23])).
% 3.55/0.99  
% 3.55/0.99  fof(f15,conjecture,(
% 3.55/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f16,negated_conjecture,(
% 3.55/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.55/0.99    inference(negated_conjecture,[],[f15])).
% 3.55/0.99  
% 3.55/0.99  fof(f33,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f16])).
% 3.55/0.99  
% 3.55/0.99  fof(f34,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.55/0.99    inference(flattening,[],[f33])).
% 3.55/0.99  
% 3.55/0.99  fof(f39,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.55/0.99    inference(nnf_transformation,[],[f34])).
% 3.55/0.99  
% 3.55/0.99  fof(f40,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.55/0.99    inference(flattening,[],[f39])).
% 3.55/0.99  
% 3.55/0.99  fof(f45,plain,(
% 3.55/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f44,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & (r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f43,plain,(
% 3.55/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f42,plain,(
% 3.55/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f41,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f46,plain,(
% 3.55/0.99    (((((~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & (r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f45,f44,f43,f42,f41])).
% 3.55/0.99  
% 3.55/0.99  fof(f69,plain,(
% 3.55/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f13,axiom,(
% 3.55/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f30,plain,(
% 3.55/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.99    inference(ennf_transformation,[],[f13])).
% 3.55/0.99  
% 3.55/0.99  fof(f62,plain,(
% 3.55/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f30])).
% 3.55/0.99  
% 3.55/0.99  fof(f72,plain,(
% 3.55/0.99    r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f12,axiom,(
% 3.55/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f29,plain,(
% 3.55/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.99    inference(ennf_transformation,[],[f12])).
% 3.55/0.99  
% 3.55/0.99  fof(f61,plain,(
% 3.55/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f29])).
% 3.55/0.99  
% 3.55/0.99  fof(f11,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f27,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.55/0.99    inference(ennf_transformation,[],[f11])).
% 3.55/0.99  
% 3.55/0.99  fof(f28,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(flattening,[],[f27])).
% 3.55/0.99  
% 3.55/0.99  fof(f60,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f28])).
% 3.55/0.99  
% 3.55/0.99  fof(f67,plain,(
% 3.55/0.99    v1_funct_1(sK3)),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f6,axiom,(
% 3.55/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f21,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f6])).
% 3.55/0.99  
% 3.55/0.99  fof(f55,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f21])).
% 3.55/0.99  
% 3.55/0.99  fof(f7,axiom,(
% 3.55/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f56,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f7])).
% 3.55/0.99  
% 3.55/0.99  fof(f73,plain,(
% 3.55/0.99    ~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f14,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f31,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.55/0.99    inference(ennf_transformation,[],[f14])).
% 3.55/0.99  
% 3.55/0.99  fof(f32,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.55/0.99    inference(flattening,[],[f31])).
% 3.55/0.99  
% 3.55/0.99  fof(f63,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f32])).
% 3.55/0.99  
% 3.55/0.99  fof(f68,plain,(
% 3.55/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f1,axiom,(
% 3.55/0.99    v1_xboole_0(k1_xboole_0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f47,plain,(
% 3.55/0.99    v1_xboole_0(k1_xboole_0)),
% 3.55/0.99    inference(cnf_transformation,[],[f1])).
% 3.55/0.99  
% 3.55/0.99  fof(f66,plain,(
% 3.55/0.99    ~v1_xboole_0(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  fof(f9,axiom,(
% 3.55/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f24,plain,(
% 3.55/0.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f9])).
% 3.55/0.99  
% 3.55/0.99  fof(f58,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f24])).
% 3.55/0.99  
% 3.55/0.99  fof(f10,axiom,(
% 3.55/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f25,plain,(
% 3.55/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.55/0.99    inference(ennf_transformation,[],[f10])).
% 3.55/0.99  
% 3.55/0.99  fof(f26,plain,(
% 3.55/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.55/0.99    inference(flattening,[],[f25])).
% 3.55/0.99  
% 3.55/0.99  fof(f59,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f26])).
% 3.55/0.99  
% 3.55/0.99  fof(f4,axiom,(
% 3.55/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f53,plain,(
% 3.55/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f4])).
% 3.55/0.99  
% 3.55/0.99  fof(f5,axiom,(
% 3.55/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f19,plain,(
% 3.55/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f5])).
% 3.55/0.99  
% 3.55/0.99  fof(f20,plain,(
% 3.55/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.55/0.99    inference(flattening,[],[f19])).
% 3.55/0.99  
% 3.55/0.99  fof(f54,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f20])).
% 3.55/0.99  
% 3.55/0.99  fof(f3,axiom,(
% 3.55/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f35,plain,(
% 3.55/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.55/0.99    inference(nnf_transformation,[],[f3])).
% 3.55/0.99  
% 3.55/0.99  fof(f36,plain,(
% 3.55/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.55/0.99    inference(rectify,[],[f35])).
% 3.55/0.99  
% 3.55/0.99  fof(f37,plain,(
% 3.55/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f38,plain,(
% 3.55/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f49,plain,(
% 3.55/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.55/0.99    inference(cnf_transformation,[],[f38])).
% 3.55/0.99  
% 3.55/0.99  fof(f75,plain,(
% 3.55/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.55/0.99    inference(equality_resolution,[],[f49])).
% 3.55/0.99  
% 3.55/0.99  fof(f70,plain,(
% 3.55/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.55/0.99    inference(cnf_transformation,[],[f46])).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2244,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK5) | r1_tarski(X0,sK5) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3875,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
% 3.55/0.99      | r1_tarski(X0,sK5)
% 3.55/0.99      | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_2244]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7784,plain,
% 3.55/0.99      ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
% 3.55/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
% 3.55/0.99      | r1_tarski(k9_relat_1(sK3,sK4),sK5) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_3875]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_10,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1)
% 3.55/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.55/0.99      | ~ v1_relat_1(X2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2924,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1)
% 3.55/0.99      | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
% 3.55/0.99      | ~ v1_relat_1(sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4139,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,X0))
% 3.55/0.99      | ~ r1_tarski(sK4,X0)
% 3.55/0.99      | ~ v1_relat_1(sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_2924]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7782,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
% 3.55/0.99      | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5))
% 3.55/0.99      | ~ v1_relat_1(sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_4139]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6514,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.55/0.99      | ~ r1_tarski(sK4,X0)
% 3.55/0.99      | r1_tarski(sK4,k1_relat_1(sK3)) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6516,plain,
% 3.55/0.99      ( ~ r1_tarski(sK1,k1_relat_1(sK3))
% 3.55/0.99      | r1_tarski(sK4,k1_relat_1(sK3))
% 3.55/0.99      | ~ r1_tarski(sK4,sK1) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_6514]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_22,negated_conjecture,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.55/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1930,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_15,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.55/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1935,plain,
% 3.55/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.55/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2573,plain,
% 3.55/0.99      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1930,c_1935]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_19,negated_conjecture,
% 3.55/0.99      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 3.55/0.99      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1933,plain,
% 3.55/0.99      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 3.55/0.99      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3075,plain,
% 3.55/0.99      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 3.55/0.99      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_2573,c_1933]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_14,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.55/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1936,plain,
% 3.55/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.55/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2692,plain,
% 3.55/0.99      ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1930,c_1936]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4048,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 3.55/0.99      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_3075,c_2692]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_13,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.55/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.55/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.55/0.99      | ~ v1_funct_1(X1)
% 3.55/0.99      | ~ v1_relat_1(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_24,negated_conjecture,
% 3.55/0.99      ( v1_funct_1(sK3) ),
% 3.55/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_445,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.55/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.55/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.55/0.99      | ~ v1_relat_1(X1)
% 3.55/0.99      | sK3 != X1 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_446,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(sK3,X1))
% 3.55/0.99      | ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.55/0.99      | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
% 3.55/0.99      | ~ v1_relat_1(sK3) ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1926,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.55/0.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.55/0.99      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.55/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_31,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_447,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.55/0.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.55/0.99      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.55/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_8,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/0.99      | ~ v1_relat_1(X1)
% 3.55/0.99      | v1_relat_1(X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2097,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.99      | v1_relat_1(X0)
% 3.55/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2304,plain,
% 3.55/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.55/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.55/0.99      | v1_relat_1(sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_2097]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2305,plain,
% 3.55/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.55/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.55/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_2304]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_9,plain,
% 3.55/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2474,plain,
% 3.55/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2475,plain,
% 3.55/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_2474]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2494,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.55/0.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.55/0.99      | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_1926,c_31,c_447,c_2305,c_2475]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2495,plain,
% 3.55/0.99      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.55/0.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.55/0.99      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
% 3.55/0.99      inference(renaming,[status(thm)],[c_2494]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4053,plain,
% 3.55/0.99      ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
% 3.55/0.99      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_4048,c_2495]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_18,negated_conjecture,
% 3.55/0.99      ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 3.55/0.99      | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1934,plain,
% 3.55/0.99      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 3.55/0.99      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3076,plain,
% 3.55/0.99      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 3.55/0.99      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_2573,c_1934]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3924,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 3.55/0.99      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_3076,c_2692]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4923,plain,
% 3.55/0.99      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 3.55/0.99      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_4053,c_3924]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4937,plain,
% 3.55/0.99      ( ~ r1_tarski(k9_relat_1(sK3,sK4),sK5)
% 3.55/0.99      | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
% 3.55/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4923]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4072,plain,
% 3.55/0.99      ( r1_tarski(sK4,k10_relat_1(sK3,sK5))
% 3.55/0.99      | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
% 3.55/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4053]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_17,plain,
% 3.55/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.55/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.99      | ~ v1_funct_1(X0)
% 3.55/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.55/0.99      | k1_xboole_0 = X2 ),
% 3.55/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_23,negated_conjecture,
% 3.55/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_420,plain,
% 3.55/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.99      | ~ v1_funct_1(X0)
% 3.55/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.55/0.99      | sK3 != X0
% 3.55/0.99      | sK2 != X2
% 3.55/0.99      | sK1 != X1
% 3.55/0.99      | k1_xboole_0 = X2 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_421,plain,
% 3.55/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.55/0.99      | ~ v1_funct_1(sK3)
% 3.55/0.99      | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
% 3.55/0.99      | k1_xboole_0 = sK2 ),
% 3.55/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_423,plain,
% 3.55/0.99      ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1 | k1_xboole_0 = sK2 ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_421,c_24,c_22]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3087,plain,
% 3.55/0.99      ( k10_relat_1(sK3,sK2) = sK1 | sK2 = k1_xboole_0 ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_423,c_2573]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_0,plain,
% 3.55/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_25,negated_conjecture,
% 3.55/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_362,plain,
% 3.55/0.99      ( sK2 != k1_xboole_0 ),
% 3.55/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_4024,plain,
% 3.55/0.99      ( k10_relat_1(sK3,sK2) = sK1 ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/1.00                [c_3087,c_362]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11,plain,
% 3.55/1.00      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1937,plain,
% 3.55/1.00      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_4027,plain,
% 3.55/1.00      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 3.55/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_4024,c_1937]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_4044,plain,
% 3.55/1.00      ( r1_tarski(sK1,k1_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.55/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4027]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_12,plain,
% 3.55/1.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.55/1.00      | ~ v1_funct_1(X0)
% 3.55/1.00      | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_433,plain,
% 3.55/1.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.55/1.00      | ~ v1_relat_1(X0)
% 3.55/1.00      | sK3 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_434,plain,
% 3.55/1.00      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0)
% 3.55/1.00      | ~ v1_relat_1(sK3) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_433]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2955,plain,
% 3.55/1.00      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
% 3.55/1.00      | ~ v1_relat_1(sK3) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_434]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1374,plain,( X0 = X0 ),theory(equality) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1399,plain,
% 3.55/1.00      ( sK1 = sK1 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1374]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1377,plain,
% 3.55/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.55/1.00      theory(equality) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1388,plain,
% 3.55/1.00      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1377]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6,plain,
% 3.55/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_370,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_371,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_5,plain,
% 3.55/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_920,plain,
% 3.55/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.55/1.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_921,plain,
% 3.55/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_920]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_975,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.55/1.00      inference(bin_hyper_res,[status(thm)],[c_371,c_921]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_21,negated_conjecture,
% 3.55/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1078,plain,
% 3.55/1.00      ( r1_tarski(X0,X1)
% 3.55/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 3.55/1.00      | sK4 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_975,c_21]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1079,plain,
% 3.55/1.00      ( r1_tarski(sK4,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1078]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1081,plain,
% 3.55/1.00      ( r1_tarski(sK4,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(contradiction,plain,
% 3.55/1.00      ( $false ),
% 3.55/1.00      inference(minisat,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_7784,c_7782,c_6516,c_4937,c_4072,c_4044,c_2955,c_2474,
% 3.55/1.00                 c_2304,c_1399,c_1388,c_1081,c_22]) ).
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  ------                               Statistics
% 3.55/1.00  
% 3.55/1.00  ------ General
% 3.55/1.00  
% 3.55/1.00  abstr_ref_over_cycles:                  0
% 3.55/1.00  abstr_ref_under_cycles:                 0
% 3.55/1.00  gc_basic_clause_elim:                   0
% 3.55/1.00  forced_gc_time:                         0
% 3.55/1.00  parsing_time:                           0.015
% 3.55/1.00  unif_index_cands_time:                  0.
% 3.55/1.00  unif_index_add_time:                    0.
% 3.55/1.00  orderings_time:                         0.
% 3.55/1.00  out_proof_time:                         0.011
% 3.55/1.00  total_time:                             0.22
% 3.55/1.00  num_of_symbols:                         52
% 3.55/1.00  num_of_terms:                           7440
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing
% 3.55/1.00  
% 3.55/1.00  num_of_splits:                          0
% 3.55/1.00  num_of_split_atoms:                     0
% 3.55/1.00  num_of_reused_defs:                     0
% 3.55/1.00  num_eq_ax_congr_red:                    12
% 3.55/1.00  num_of_sem_filtered_clauses:            1
% 3.55/1.00  num_of_subtypes:                        0
% 3.55/1.00  monotx_restored_types:                  0
% 3.55/1.00  sat_num_of_epr_types:                   0
% 3.55/1.00  sat_num_of_non_cyclic_types:            0
% 3.55/1.00  sat_guarded_non_collapsed_types:        0
% 3.55/1.00  num_pure_diseq_elim:                    0
% 3.55/1.00  simp_replaced_by:                       0
% 3.55/1.00  res_preprocessed:                       129
% 3.55/1.00  prep_upred:                             0
% 3.55/1.00  prep_unflattend:                        68
% 3.55/1.00  smt_new_axioms:                         0
% 3.55/1.00  pred_elim_cands:                        4
% 3.55/1.00  pred_elim:                              3
% 3.55/1.00  pred_elim_cl:                           2
% 3.55/1.00  pred_elim_cycles:                       7
% 3.55/1.00  merged_defs:                            16
% 3.55/1.00  merged_defs_ncl:                        0
% 3.55/1.00  bin_hyper_res:                          17
% 3.55/1.00  prep_cycles:                            4
% 3.55/1.00  pred_elim_time:                         0.013
% 3.55/1.00  splitting_time:                         0.
% 3.55/1.00  sem_filter_time:                        0.
% 3.55/1.00  monotx_time:                            0.001
% 3.55/1.00  subtype_inf_time:                       0.
% 3.55/1.00  
% 3.55/1.00  ------ Problem properties
% 3.55/1.00  
% 3.55/1.00  clauses:                                25
% 3.55/1.00  conjectures:                            5
% 3.55/1.00  epr:                                    5
% 3.55/1.00  horn:                                   22
% 3.55/1.00  ground:                                 8
% 3.55/1.00  unary:                                  7
% 3.55/1.00  binary:                                 12
% 3.55/1.00  lits:                                   50
% 3.55/1.00  lits_eq:                                9
% 3.55/1.00  fd_pure:                                0
% 3.55/1.00  fd_pseudo:                              0
% 3.55/1.00  fd_cond:                                0
% 3.55/1.00  fd_pseudo_cond:                         2
% 3.55/1.00  ac_symbols:                             0
% 3.55/1.00  
% 3.55/1.00  ------ Propositional Solver
% 3.55/1.00  
% 3.55/1.00  prop_solver_calls:                      28
% 3.55/1.00  prop_fast_solver_calls:                 917
% 3.55/1.00  smt_solver_calls:                       0
% 3.55/1.00  smt_fast_solver_calls:                  0
% 3.55/1.00  prop_num_of_clauses:                    2908
% 3.55/1.00  prop_preprocess_simplified:             7831
% 3.55/1.00  prop_fo_subsumed:                       23
% 3.55/1.00  prop_solver_time:                       0.
% 3.55/1.00  smt_solver_time:                        0.
% 3.55/1.00  smt_fast_solver_time:                   0.
% 3.55/1.00  prop_fast_solver_time:                  0.
% 3.55/1.00  prop_unsat_core_time:                   0.
% 3.55/1.00  
% 3.55/1.00  ------ QBF
% 3.55/1.00  
% 3.55/1.00  qbf_q_res:                              0
% 3.55/1.00  qbf_num_tautologies:                    0
% 3.55/1.00  qbf_prep_cycles:                        0
% 3.55/1.00  
% 3.55/1.00  ------ BMC1
% 3.55/1.00  
% 3.55/1.00  bmc1_current_bound:                     -1
% 3.55/1.00  bmc1_last_solved_bound:                 -1
% 3.55/1.00  bmc1_unsat_core_size:                   -1
% 3.55/1.00  bmc1_unsat_core_parents_size:           -1
% 3.55/1.00  bmc1_merge_next_fun:                    0
% 3.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation
% 3.55/1.00  
% 3.55/1.00  inst_num_of_clauses:                    798
% 3.55/1.00  inst_num_in_passive:                    318
% 3.55/1.00  inst_num_in_active:                     325
% 3.55/1.00  inst_num_in_unprocessed:                154
% 3.55/1.00  inst_num_of_loops:                      394
% 3.55/1.00  inst_num_of_learning_restarts:          0
% 3.55/1.00  inst_num_moves_active_passive:          66
% 3.55/1.00  inst_lit_activity:                      0
% 3.55/1.00  inst_lit_activity_moves:                0
% 3.55/1.00  inst_num_tautologies:                   0
% 3.55/1.00  inst_num_prop_implied:                  0
% 3.55/1.00  inst_num_existing_simplified:           0
% 3.55/1.00  inst_num_eq_res_simplified:             0
% 3.55/1.00  inst_num_child_elim:                    0
% 3.55/1.00  inst_num_of_dismatching_blockings:      308
% 3.55/1.00  inst_num_of_non_proper_insts:           546
% 3.55/1.00  inst_num_of_duplicates:                 0
% 3.55/1.00  inst_inst_num_from_inst_to_res:         0
% 3.55/1.00  inst_dismatching_checking_time:         0.
% 3.55/1.00  
% 3.55/1.00  ------ Resolution
% 3.55/1.00  
% 3.55/1.00  res_num_of_clauses:                     0
% 3.55/1.00  res_num_in_passive:                     0
% 3.55/1.00  res_num_in_active:                      0
% 3.55/1.00  res_num_of_loops:                       133
% 3.55/1.00  res_forward_subset_subsumed:            40
% 3.55/1.00  res_backward_subset_subsumed:           0
% 3.55/1.00  res_forward_subsumed:                   0
% 3.55/1.00  res_backward_subsumed:                  0
% 3.55/1.00  res_forward_subsumption_resolution:     0
% 3.55/1.00  res_backward_subsumption_resolution:    0
% 3.55/1.00  res_clause_to_clause_subsumption:       418
% 3.55/1.00  res_orphan_elimination:                 0
% 3.55/1.00  res_tautology_del:                      112
% 3.55/1.00  res_num_eq_res_simplified:              0
% 3.55/1.00  res_num_sel_changes:                    0
% 3.55/1.00  res_moves_from_active_to_pass:          0
% 3.55/1.00  
% 3.55/1.00  ------ Superposition
% 3.55/1.00  
% 3.55/1.00  sup_time_total:                         0.
% 3.55/1.00  sup_time_generating:                    0.
% 3.55/1.00  sup_time_sim_full:                      0.
% 3.55/1.00  sup_time_sim_immed:                     0.
% 3.55/1.00  
% 3.55/1.00  sup_num_of_clauses:                     165
% 3.55/1.00  sup_num_in_active:                      76
% 3.55/1.00  sup_num_in_passive:                     89
% 3.55/1.00  sup_num_of_loops:                       78
% 3.55/1.00  sup_fw_superposition:                   71
% 3.55/1.00  sup_bw_superposition:                   98
% 3.55/1.00  sup_immediate_simplified:               11
% 3.55/1.00  sup_given_eliminated:                   0
% 3.55/1.00  comparisons_done:                       0
% 3.55/1.00  comparisons_avoided:                    0
% 3.55/1.00  
% 3.55/1.00  ------ Simplifications
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  sim_fw_subset_subsumed:                 4
% 3.55/1.00  sim_bw_subset_subsumed:                 1
% 3.55/1.00  sim_fw_subsumed:                        2
% 3.55/1.00  sim_bw_subsumed:                        0
% 3.55/1.00  sim_fw_subsumption_res:                 0
% 3.55/1.00  sim_bw_subsumption_res:                 0
% 3.55/1.00  sim_tautology_del:                      15
% 3.55/1.00  sim_eq_tautology_del:                   1
% 3.55/1.00  sim_eq_res_simp:                        0
% 3.55/1.00  sim_fw_demodulated:                     3
% 3.55/1.00  sim_bw_demodulated:                     2
% 3.55/1.00  sim_light_normalised:                   5
% 3.55/1.00  sim_joinable_taut:                      0
% 3.55/1.00  sim_joinable_simp:                      0
% 3.55/1.00  sim_ac_normalised:                      0
% 3.55/1.00  sim_smt_subsumption:                    0
% 3.55/1.00  
%------------------------------------------------------------------------------
