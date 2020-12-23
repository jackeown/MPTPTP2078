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
% DateTime   : Thu Dec  3 12:09:08 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 393 expanded)
%              Number of clauses        :   76 ( 105 expanded)
%              Number of leaves         :   22 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  500 (3032 expanded)
%              Number of equality atoms :   97 ( 123 expanded)
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

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f38])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f39,f44,f43,f42,f41,f40])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,
    ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2303,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,X1)))
    | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X1)),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4118,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1)
    | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k10_relat_1(sK3,X1)))
    | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X1)),X1) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_13501,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
    | ~ r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
    | r1_tarski(k9_relat_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_4118])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2241,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3335,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,X0))
    | ~ r1_tarski(sK4,X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_4974,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
    | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3335])).

cnf(c_4324,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4326,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(sK3))
    | ~ r1_tarski(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_4324])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1998,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2003,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2892,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1998,c_2003])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2001,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3240,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2892,c_2001])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2004,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2897,plain,
    ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1998,c_2004])).

cnf(c_3437,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3240,c_2897])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_434,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_435,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1994,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_436,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2158,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_2664,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1994,c_30,c_436,c_2159])).

cnf(c_2665,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2664])).

cnf(c_3442,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_2665])).

cnf(c_3456,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5))
    | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3442])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_410,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_23,c_21])).

cnf(c_3252,plain,
    ( k10_relat_1(sK3,sK2) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_412,c_2892])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_351,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_3418,plain,
    ( k10_relat_1(sK3,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3252,c_351])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2006,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3421,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_2006])).

cnf(c_3433,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3421])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2002,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3241,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2892,c_2002])).

cnf(c_3304,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3241,c_2897])).

cnf(c_3307,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3304])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_422,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_423,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_2479,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1458,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1483,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1461,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1472,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_962,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_963,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_962])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_360,c_963])).

cnf(c_1259,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1015])).

cnf(c_1260,plain,
    ( r1_tarski(sK4,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_1259])).

cnf(c_1262,plain,
    ( r1_tarski(sK4,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13501,c_4974,c_4326,c_3456,c_3433,c_3307,c_2479,c_2158,c_1483,c_1472,c_1262,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.50/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.03  
% 3.50/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.03  
% 3.50/1.03  ------  iProver source info
% 3.50/1.03  
% 3.50/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.03  git: non_committed_changes: false
% 3.50/1.03  git: last_make_outside_of_git: false
% 3.50/1.03  
% 3.50/1.03  ------ 
% 3.50/1.03  
% 3.50/1.03  ------ Input Options
% 3.50/1.03  
% 3.50/1.03  --out_options                           all
% 3.50/1.03  --tptp_safe_out                         true
% 3.50/1.03  --problem_path                          ""
% 3.50/1.03  --include_path                          ""
% 3.50/1.03  --clausifier                            res/vclausify_rel
% 3.50/1.03  --clausifier_options                    --mode clausify
% 3.50/1.03  --stdin                                 false
% 3.50/1.03  --stats_out                             all
% 3.50/1.03  
% 3.50/1.03  ------ General Options
% 3.50/1.03  
% 3.50/1.03  --fof                                   false
% 3.50/1.03  --time_out_real                         305.
% 3.50/1.03  --time_out_virtual                      -1.
% 3.50/1.03  --symbol_type_check                     false
% 3.50/1.03  --clausify_out                          false
% 3.50/1.03  --sig_cnt_out                           false
% 3.50/1.03  --trig_cnt_out                          false
% 3.50/1.03  --trig_cnt_out_tolerance                1.
% 3.50/1.03  --trig_cnt_out_sk_spl                   false
% 3.50/1.03  --abstr_cl_out                          false
% 3.50/1.03  
% 3.50/1.03  ------ Global Options
% 3.50/1.03  
% 3.50/1.03  --schedule                              default
% 3.50/1.03  --add_important_lit                     false
% 3.50/1.03  --prop_solver_per_cl                    1000
% 3.50/1.03  --min_unsat_core                        false
% 3.50/1.03  --soft_assumptions                      false
% 3.50/1.03  --soft_lemma_size                       3
% 3.50/1.03  --prop_impl_unit_size                   0
% 3.50/1.03  --prop_impl_unit                        []
% 3.50/1.03  --share_sel_clauses                     true
% 3.50/1.03  --reset_solvers                         false
% 3.50/1.03  --bc_imp_inh                            [conj_cone]
% 3.50/1.03  --conj_cone_tolerance                   3.
% 3.50/1.03  --extra_neg_conj                        none
% 3.50/1.03  --large_theory_mode                     true
% 3.50/1.03  --prolific_symb_bound                   200
% 3.50/1.03  --lt_threshold                          2000
% 3.50/1.03  --clause_weak_htbl                      true
% 3.50/1.03  --gc_record_bc_elim                     false
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing Options
% 3.50/1.03  
% 3.50/1.03  --preprocessing_flag                    true
% 3.50/1.03  --time_out_prep_mult                    0.1
% 3.50/1.03  --splitting_mode                        input
% 3.50/1.03  --splitting_grd                         true
% 3.50/1.03  --splitting_cvd                         false
% 3.50/1.03  --splitting_cvd_svl                     false
% 3.50/1.03  --splitting_nvd                         32
% 3.50/1.03  --sub_typing                            true
% 3.50/1.03  --prep_gs_sim                           true
% 3.50/1.03  --prep_unflatten                        true
% 3.50/1.03  --prep_res_sim                          true
% 3.50/1.03  --prep_upred                            true
% 3.50/1.03  --prep_sem_filter                       exhaustive
% 3.50/1.03  --prep_sem_filter_out                   false
% 3.50/1.03  --pred_elim                             true
% 3.50/1.03  --res_sim_input                         true
% 3.50/1.03  --eq_ax_congr_red                       true
% 3.50/1.03  --pure_diseq_elim                       true
% 3.50/1.03  --brand_transform                       false
% 3.50/1.03  --non_eq_to_eq                          false
% 3.50/1.03  --prep_def_merge                        true
% 3.50/1.03  --prep_def_merge_prop_impl              false
% 3.50/1.03  --prep_def_merge_mbd                    true
% 3.50/1.03  --prep_def_merge_tr_red                 false
% 3.50/1.03  --prep_def_merge_tr_cl                  false
% 3.50/1.03  --smt_preprocessing                     true
% 3.50/1.03  --smt_ac_axioms                         fast
% 3.50/1.03  --preprocessed_out                      false
% 3.50/1.03  --preprocessed_stats                    false
% 3.50/1.03  
% 3.50/1.03  ------ Abstraction refinement Options
% 3.50/1.03  
% 3.50/1.03  --abstr_ref                             []
% 3.50/1.03  --abstr_ref_prep                        false
% 3.50/1.03  --abstr_ref_until_sat                   false
% 3.50/1.03  --abstr_ref_sig_restrict                funpre
% 3.50/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.03  --abstr_ref_under                       []
% 3.50/1.03  
% 3.50/1.03  ------ SAT Options
% 3.50/1.03  
% 3.50/1.03  --sat_mode                              false
% 3.50/1.03  --sat_fm_restart_options                ""
% 3.50/1.03  --sat_gr_def                            false
% 3.50/1.03  --sat_epr_types                         true
% 3.50/1.03  --sat_non_cyclic_types                  false
% 3.50/1.03  --sat_finite_models                     false
% 3.50/1.03  --sat_fm_lemmas                         false
% 3.50/1.03  --sat_fm_prep                           false
% 3.50/1.03  --sat_fm_uc_incr                        true
% 3.50/1.03  --sat_out_model                         small
% 3.50/1.03  --sat_out_clauses                       false
% 3.50/1.03  
% 3.50/1.03  ------ QBF Options
% 3.50/1.03  
% 3.50/1.03  --qbf_mode                              false
% 3.50/1.03  --qbf_elim_univ                         false
% 3.50/1.03  --qbf_dom_inst                          none
% 3.50/1.03  --qbf_dom_pre_inst                      false
% 3.50/1.03  --qbf_sk_in                             false
% 3.50/1.03  --qbf_pred_elim                         true
% 3.50/1.03  --qbf_split                             512
% 3.50/1.03  
% 3.50/1.03  ------ BMC1 Options
% 3.50/1.03  
% 3.50/1.03  --bmc1_incremental                      false
% 3.50/1.03  --bmc1_axioms                           reachable_all
% 3.50/1.03  --bmc1_min_bound                        0
% 3.50/1.03  --bmc1_max_bound                        -1
% 3.50/1.03  --bmc1_max_bound_default                -1
% 3.50/1.03  --bmc1_symbol_reachability              true
% 3.50/1.03  --bmc1_property_lemmas                  false
% 3.50/1.03  --bmc1_k_induction                      false
% 3.50/1.03  --bmc1_non_equiv_states                 false
% 3.50/1.03  --bmc1_deadlock                         false
% 3.50/1.03  --bmc1_ucm                              false
% 3.50/1.03  --bmc1_add_unsat_core                   none
% 3.50/1.03  --bmc1_unsat_core_children              false
% 3.50/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.03  --bmc1_out_stat                         full
% 3.50/1.03  --bmc1_ground_init                      false
% 3.50/1.03  --bmc1_pre_inst_next_state              false
% 3.50/1.03  --bmc1_pre_inst_state                   false
% 3.50/1.03  --bmc1_pre_inst_reach_state             false
% 3.50/1.03  --bmc1_out_unsat_core                   false
% 3.50/1.03  --bmc1_aig_witness_out                  false
% 3.50/1.03  --bmc1_verbose                          false
% 3.50/1.03  --bmc1_dump_clauses_tptp                false
% 3.50/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.03  --bmc1_dump_file                        -
% 3.50/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.03  --bmc1_ucm_extend_mode                  1
% 3.50/1.03  --bmc1_ucm_init_mode                    2
% 3.50/1.03  --bmc1_ucm_cone_mode                    none
% 3.50/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.03  --bmc1_ucm_relax_model                  4
% 3.50/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.03  --bmc1_ucm_layered_model                none
% 3.50/1.03  --bmc1_ucm_max_lemma_size               10
% 3.50/1.03  
% 3.50/1.03  ------ AIG Options
% 3.50/1.03  
% 3.50/1.03  --aig_mode                              false
% 3.50/1.03  
% 3.50/1.03  ------ Instantiation Options
% 3.50/1.03  
% 3.50/1.03  --instantiation_flag                    true
% 3.50/1.03  --inst_sos_flag                         false
% 3.50/1.03  --inst_sos_phase                        true
% 3.50/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.03  --inst_lit_sel_side                     num_symb
% 3.50/1.03  --inst_solver_per_active                1400
% 3.50/1.03  --inst_solver_calls_frac                1.
% 3.50/1.03  --inst_passive_queue_type               priority_queues
% 3.50/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.03  --inst_passive_queues_freq              [25;2]
% 3.50/1.03  --inst_dismatching                      true
% 3.50/1.03  --inst_eager_unprocessed_to_passive     true
% 3.50/1.03  --inst_prop_sim_given                   true
% 3.50/1.03  --inst_prop_sim_new                     false
% 3.50/1.03  --inst_subs_new                         false
% 3.50/1.03  --inst_eq_res_simp                      false
% 3.50/1.03  --inst_subs_given                       false
% 3.50/1.03  --inst_orphan_elimination               true
% 3.50/1.03  --inst_learning_loop_flag               true
% 3.50/1.03  --inst_learning_start                   3000
% 3.50/1.03  --inst_learning_factor                  2
% 3.50/1.03  --inst_start_prop_sim_after_learn       3
% 3.50/1.03  --inst_sel_renew                        solver
% 3.50/1.03  --inst_lit_activity_flag                true
% 3.50/1.03  --inst_restr_to_given                   false
% 3.50/1.03  --inst_activity_threshold               500
% 3.50/1.03  --inst_out_proof                        true
% 3.50/1.03  
% 3.50/1.03  ------ Resolution Options
% 3.50/1.03  
% 3.50/1.03  --resolution_flag                       true
% 3.50/1.03  --res_lit_sel                           adaptive
% 3.50/1.03  --res_lit_sel_side                      none
% 3.50/1.03  --res_ordering                          kbo
% 3.50/1.03  --res_to_prop_solver                    active
% 3.50/1.03  --res_prop_simpl_new                    false
% 3.50/1.03  --res_prop_simpl_given                  true
% 3.50/1.03  --res_passive_queue_type                priority_queues
% 3.50/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.03  --res_passive_queues_freq               [15;5]
% 3.50/1.03  --res_forward_subs                      full
% 3.50/1.03  --res_backward_subs                     full
% 3.50/1.03  --res_forward_subs_resolution           true
% 3.50/1.03  --res_backward_subs_resolution          true
% 3.50/1.03  --res_orphan_elimination                true
% 3.50/1.03  --res_time_limit                        2.
% 3.50/1.03  --res_out_proof                         true
% 3.50/1.03  
% 3.50/1.03  ------ Superposition Options
% 3.50/1.03  
% 3.50/1.03  --superposition_flag                    true
% 3.50/1.03  --sup_passive_queue_type                priority_queues
% 3.50/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.03  --demod_completeness_check              fast
% 3.50/1.03  --demod_use_ground                      true
% 3.50/1.03  --sup_to_prop_solver                    passive
% 3.50/1.03  --sup_prop_simpl_new                    true
% 3.50/1.03  --sup_prop_simpl_given                  true
% 3.50/1.03  --sup_fun_splitting                     false
% 3.50/1.03  --sup_smt_interval                      50000
% 3.50/1.03  
% 3.50/1.03  ------ Superposition Simplification Setup
% 3.50/1.03  
% 3.50/1.03  --sup_indices_passive                   []
% 3.50/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_full_bw                           [BwDemod]
% 3.50/1.03  --sup_immed_triv                        [TrivRules]
% 3.50/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_immed_bw_main                     []
% 3.50/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.03  
% 3.50/1.03  ------ Combination Options
% 3.50/1.03  
% 3.50/1.03  --comb_res_mult                         3
% 3.50/1.03  --comb_sup_mult                         2
% 3.50/1.03  --comb_inst_mult                        10
% 3.50/1.03  
% 3.50/1.03  ------ Debug Options
% 3.50/1.03  
% 3.50/1.03  --dbg_backtrace                         false
% 3.50/1.03  --dbg_dump_prop_clauses                 false
% 3.50/1.03  --dbg_dump_prop_clauses_file            -
% 3.50/1.03  --dbg_out_stat                          false
% 3.50/1.03  ------ Parsing...
% 3.50/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.03  ------ Proving...
% 3.50/1.03  ------ Problem Properties 
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  clauses                                 24
% 3.50/1.03  conjectures                             5
% 3.50/1.03  EPR                                     5
% 3.50/1.03  Horn                                    21
% 3.50/1.03  unary                                   6
% 3.50/1.03  binary                                  13
% 3.50/1.03  lits                                    48
% 3.50/1.03  lits eq                                 9
% 3.50/1.03  fd_pure                                 0
% 3.50/1.03  fd_pseudo                               0
% 3.50/1.03  fd_cond                                 0
% 3.50/1.03  fd_pseudo_cond                          2
% 3.50/1.03  AC symbols                              0
% 3.50/1.03  
% 3.50/1.03  ------ Schedule dynamic 5 is on 
% 3.50/1.03  
% 3.50/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  ------ 
% 3.50/1.03  Current options:
% 3.50/1.03  ------ 
% 3.50/1.03  
% 3.50/1.03  ------ Input Options
% 3.50/1.03  
% 3.50/1.03  --out_options                           all
% 3.50/1.03  --tptp_safe_out                         true
% 3.50/1.03  --problem_path                          ""
% 3.50/1.03  --include_path                          ""
% 3.50/1.03  --clausifier                            res/vclausify_rel
% 3.50/1.03  --clausifier_options                    --mode clausify
% 3.50/1.03  --stdin                                 false
% 3.50/1.03  --stats_out                             all
% 3.50/1.03  
% 3.50/1.03  ------ General Options
% 3.50/1.03  
% 3.50/1.03  --fof                                   false
% 3.50/1.03  --time_out_real                         305.
% 3.50/1.03  --time_out_virtual                      -1.
% 3.50/1.03  --symbol_type_check                     false
% 3.50/1.03  --clausify_out                          false
% 3.50/1.03  --sig_cnt_out                           false
% 3.50/1.03  --trig_cnt_out                          false
% 3.50/1.03  --trig_cnt_out_tolerance                1.
% 3.50/1.03  --trig_cnt_out_sk_spl                   false
% 3.50/1.03  --abstr_cl_out                          false
% 3.50/1.03  
% 3.50/1.03  ------ Global Options
% 3.50/1.03  
% 3.50/1.03  --schedule                              default
% 3.50/1.03  --add_important_lit                     false
% 3.50/1.03  --prop_solver_per_cl                    1000
% 3.50/1.03  --min_unsat_core                        false
% 3.50/1.03  --soft_assumptions                      false
% 3.50/1.03  --soft_lemma_size                       3
% 3.50/1.03  --prop_impl_unit_size                   0
% 3.50/1.03  --prop_impl_unit                        []
% 3.50/1.03  --share_sel_clauses                     true
% 3.50/1.03  --reset_solvers                         false
% 3.50/1.03  --bc_imp_inh                            [conj_cone]
% 3.50/1.03  --conj_cone_tolerance                   3.
% 3.50/1.03  --extra_neg_conj                        none
% 3.50/1.03  --large_theory_mode                     true
% 3.50/1.03  --prolific_symb_bound                   200
% 3.50/1.03  --lt_threshold                          2000
% 3.50/1.03  --clause_weak_htbl                      true
% 3.50/1.03  --gc_record_bc_elim                     false
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing Options
% 3.50/1.03  
% 3.50/1.03  --preprocessing_flag                    true
% 3.50/1.03  --time_out_prep_mult                    0.1
% 3.50/1.03  --splitting_mode                        input
% 3.50/1.03  --splitting_grd                         true
% 3.50/1.03  --splitting_cvd                         false
% 3.50/1.03  --splitting_cvd_svl                     false
% 3.50/1.03  --splitting_nvd                         32
% 3.50/1.03  --sub_typing                            true
% 3.50/1.03  --prep_gs_sim                           true
% 3.50/1.03  --prep_unflatten                        true
% 3.50/1.03  --prep_res_sim                          true
% 3.50/1.03  --prep_upred                            true
% 3.50/1.03  --prep_sem_filter                       exhaustive
% 3.50/1.03  --prep_sem_filter_out                   false
% 3.50/1.03  --pred_elim                             true
% 3.50/1.03  --res_sim_input                         true
% 3.50/1.03  --eq_ax_congr_red                       true
% 3.50/1.03  --pure_diseq_elim                       true
% 3.50/1.03  --brand_transform                       false
% 3.50/1.03  --non_eq_to_eq                          false
% 3.50/1.03  --prep_def_merge                        true
% 3.50/1.03  --prep_def_merge_prop_impl              false
% 3.50/1.03  --prep_def_merge_mbd                    true
% 3.50/1.03  --prep_def_merge_tr_red                 false
% 3.50/1.03  --prep_def_merge_tr_cl                  false
% 3.50/1.03  --smt_preprocessing                     true
% 3.50/1.03  --smt_ac_axioms                         fast
% 3.50/1.03  --preprocessed_out                      false
% 3.50/1.03  --preprocessed_stats                    false
% 3.50/1.03  
% 3.50/1.03  ------ Abstraction refinement Options
% 3.50/1.03  
% 3.50/1.03  --abstr_ref                             []
% 3.50/1.03  --abstr_ref_prep                        false
% 3.50/1.03  --abstr_ref_until_sat                   false
% 3.50/1.03  --abstr_ref_sig_restrict                funpre
% 3.50/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.03  --abstr_ref_under                       []
% 3.50/1.03  
% 3.50/1.03  ------ SAT Options
% 3.50/1.03  
% 3.50/1.03  --sat_mode                              false
% 3.50/1.03  --sat_fm_restart_options                ""
% 3.50/1.03  --sat_gr_def                            false
% 3.50/1.03  --sat_epr_types                         true
% 3.50/1.03  --sat_non_cyclic_types                  false
% 3.50/1.03  --sat_finite_models                     false
% 3.50/1.03  --sat_fm_lemmas                         false
% 3.50/1.03  --sat_fm_prep                           false
% 3.50/1.03  --sat_fm_uc_incr                        true
% 3.50/1.03  --sat_out_model                         small
% 3.50/1.03  --sat_out_clauses                       false
% 3.50/1.03  
% 3.50/1.03  ------ QBF Options
% 3.50/1.03  
% 3.50/1.03  --qbf_mode                              false
% 3.50/1.03  --qbf_elim_univ                         false
% 3.50/1.03  --qbf_dom_inst                          none
% 3.50/1.03  --qbf_dom_pre_inst                      false
% 3.50/1.03  --qbf_sk_in                             false
% 3.50/1.03  --qbf_pred_elim                         true
% 3.50/1.03  --qbf_split                             512
% 3.50/1.03  
% 3.50/1.03  ------ BMC1 Options
% 3.50/1.03  
% 3.50/1.03  --bmc1_incremental                      false
% 3.50/1.03  --bmc1_axioms                           reachable_all
% 3.50/1.03  --bmc1_min_bound                        0
% 3.50/1.03  --bmc1_max_bound                        -1
% 3.50/1.03  --bmc1_max_bound_default                -1
% 3.50/1.03  --bmc1_symbol_reachability              true
% 3.50/1.03  --bmc1_property_lemmas                  false
% 3.50/1.03  --bmc1_k_induction                      false
% 3.50/1.03  --bmc1_non_equiv_states                 false
% 3.50/1.03  --bmc1_deadlock                         false
% 3.50/1.03  --bmc1_ucm                              false
% 3.50/1.03  --bmc1_add_unsat_core                   none
% 3.50/1.03  --bmc1_unsat_core_children              false
% 3.50/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.03  --bmc1_out_stat                         full
% 3.50/1.03  --bmc1_ground_init                      false
% 3.50/1.03  --bmc1_pre_inst_next_state              false
% 3.50/1.03  --bmc1_pre_inst_state                   false
% 3.50/1.03  --bmc1_pre_inst_reach_state             false
% 3.50/1.03  --bmc1_out_unsat_core                   false
% 3.50/1.03  --bmc1_aig_witness_out                  false
% 3.50/1.03  --bmc1_verbose                          false
% 3.50/1.03  --bmc1_dump_clauses_tptp                false
% 3.50/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.03  --bmc1_dump_file                        -
% 3.50/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.03  --bmc1_ucm_extend_mode                  1
% 3.50/1.03  --bmc1_ucm_init_mode                    2
% 3.50/1.03  --bmc1_ucm_cone_mode                    none
% 3.50/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.03  --bmc1_ucm_relax_model                  4
% 3.50/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.03  --bmc1_ucm_layered_model                none
% 3.50/1.03  --bmc1_ucm_max_lemma_size               10
% 3.50/1.03  
% 3.50/1.03  ------ AIG Options
% 3.50/1.03  
% 3.50/1.03  --aig_mode                              false
% 3.50/1.03  
% 3.50/1.03  ------ Instantiation Options
% 3.50/1.03  
% 3.50/1.03  --instantiation_flag                    true
% 3.50/1.03  --inst_sos_flag                         false
% 3.50/1.03  --inst_sos_phase                        true
% 3.50/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.03  --inst_lit_sel_side                     none
% 3.50/1.03  --inst_solver_per_active                1400
% 3.50/1.03  --inst_solver_calls_frac                1.
% 3.50/1.03  --inst_passive_queue_type               priority_queues
% 3.50/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.03  --inst_passive_queues_freq              [25;2]
% 3.50/1.03  --inst_dismatching                      true
% 3.50/1.03  --inst_eager_unprocessed_to_passive     true
% 3.50/1.03  --inst_prop_sim_given                   true
% 3.50/1.03  --inst_prop_sim_new                     false
% 3.50/1.03  --inst_subs_new                         false
% 3.50/1.03  --inst_eq_res_simp                      false
% 3.50/1.03  --inst_subs_given                       false
% 3.50/1.03  --inst_orphan_elimination               true
% 3.50/1.03  --inst_learning_loop_flag               true
% 3.50/1.03  --inst_learning_start                   3000
% 3.50/1.03  --inst_learning_factor                  2
% 3.50/1.03  --inst_start_prop_sim_after_learn       3
% 3.50/1.03  --inst_sel_renew                        solver
% 3.50/1.03  --inst_lit_activity_flag                true
% 3.50/1.03  --inst_restr_to_given                   false
% 3.50/1.03  --inst_activity_threshold               500
% 3.50/1.03  --inst_out_proof                        true
% 3.50/1.03  
% 3.50/1.03  ------ Resolution Options
% 3.50/1.03  
% 3.50/1.03  --resolution_flag                       false
% 3.50/1.03  --res_lit_sel                           adaptive
% 3.50/1.03  --res_lit_sel_side                      none
% 3.50/1.03  --res_ordering                          kbo
% 3.50/1.03  --res_to_prop_solver                    active
% 3.50/1.03  --res_prop_simpl_new                    false
% 3.50/1.03  --res_prop_simpl_given                  true
% 3.50/1.03  --res_passive_queue_type                priority_queues
% 3.50/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.03  --res_passive_queues_freq               [15;5]
% 3.50/1.03  --res_forward_subs                      full
% 3.50/1.03  --res_backward_subs                     full
% 3.50/1.03  --res_forward_subs_resolution           true
% 3.50/1.03  --res_backward_subs_resolution          true
% 3.50/1.03  --res_orphan_elimination                true
% 3.50/1.03  --res_time_limit                        2.
% 3.50/1.03  --res_out_proof                         true
% 3.50/1.03  
% 3.50/1.03  ------ Superposition Options
% 3.50/1.03  
% 3.50/1.03  --superposition_flag                    true
% 3.50/1.03  --sup_passive_queue_type                priority_queues
% 3.50/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.03  --demod_completeness_check              fast
% 3.50/1.03  --demod_use_ground                      true
% 3.50/1.03  --sup_to_prop_solver                    passive
% 3.50/1.03  --sup_prop_simpl_new                    true
% 3.50/1.03  --sup_prop_simpl_given                  true
% 3.50/1.03  --sup_fun_splitting                     false
% 3.50/1.03  --sup_smt_interval                      50000
% 3.50/1.03  
% 3.50/1.03  ------ Superposition Simplification Setup
% 3.50/1.03  
% 3.50/1.03  --sup_indices_passive                   []
% 3.50/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_full_bw                           [BwDemod]
% 3.50/1.03  --sup_immed_triv                        [TrivRules]
% 3.50/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_immed_bw_main                     []
% 3.50/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.03  
% 3.50/1.03  ------ Combination Options
% 3.50/1.03  
% 3.50/1.03  --comb_res_mult                         3
% 3.50/1.03  --comb_sup_mult                         2
% 3.50/1.03  --comb_inst_mult                        10
% 3.50/1.03  
% 3.50/1.03  ------ Debug Options
% 3.50/1.03  
% 3.50/1.03  --dbg_backtrace                         false
% 3.50/1.03  --dbg_dump_prop_clauses                 false
% 3.50/1.03  --dbg_dump_prop_clauses_file            -
% 3.50/1.03  --dbg_out_stat                          false
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  ------ Proving...
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  % SZS status Theorem for theBenchmark.p
% 3.50/1.03  
% 3.50/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/1.03  
% 3.50/1.03  fof(f2,axiom,(
% 3.50/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f16,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.50/1.03    inference(ennf_transformation,[],[f2])).
% 3.50/1.03  
% 3.50/1.03  fof(f17,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.50/1.03    inference(flattening,[],[f16])).
% 3.50/1.03  
% 3.50/1.03  fof(f47,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f17])).
% 3.50/1.03  
% 3.50/1.03  fof(f6,axiom,(
% 3.50/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f20,plain,(
% 3.50/1.03    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.50/1.03    inference(ennf_transformation,[],[f6])).
% 3.50/1.03  
% 3.50/1.03  fof(f21,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.50/1.03    inference(flattening,[],[f20])).
% 3.50/1.03  
% 3.50/1.03  fof(f54,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f21])).
% 3.50/1.03  
% 3.50/1.03  fof(f14,conjecture,(
% 3.50/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f15,negated_conjecture,(
% 3.50/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.50/1.03    inference(negated_conjecture,[],[f14])).
% 3.50/1.03  
% 3.50/1.03  fof(f32,plain,(
% 3.50/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.50/1.03    inference(ennf_transformation,[],[f15])).
% 3.50/1.03  
% 3.50/1.03  fof(f33,plain,(
% 3.50/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.50/1.03    inference(flattening,[],[f32])).
% 3.50/1.03  
% 3.50/1.03  fof(f38,plain,(
% 3.50/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.50/1.03    inference(nnf_transformation,[],[f33])).
% 3.50/1.03  
% 3.50/1.03  fof(f39,plain,(
% 3.50/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.50/1.03    inference(flattening,[],[f38])).
% 3.50/1.03  
% 3.50/1.03  fof(f44,plain,(
% 3.50/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f43,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & (r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f42,plain,(
% 3.50/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f41,plain,(
% 3.50/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f40,plain,(
% 3.50/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f45,plain,(
% 3.50/1.03    (((((~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & (r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 3.50/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f39,f44,f43,f42,f41,f40])).
% 3.50/1.03  
% 3.50/1.03  fof(f67,plain,(
% 3.50/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f12,axiom,(
% 3.50/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f29,plain,(
% 3.50/1.03    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.03    inference(ennf_transformation,[],[f12])).
% 3.50/1.03  
% 3.50/1.03  fof(f60,plain,(
% 3.50/1.03    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.03    inference(cnf_transformation,[],[f29])).
% 3.50/1.03  
% 3.50/1.03  fof(f70,plain,(
% 3.50/1.03    r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f11,axiom,(
% 3.50/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f28,plain,(
% 3.50/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.03    inference(ennf_transformation,[],[f11])).
% 3.50/1.03  
% 3.50/1.03  fof(f59,plain,(
% 3.50/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.03    inference(cnf_transformation,[],[f28])).
% 3.50/1.03  
% 3.50/1.03  fof(f9,axiom,(
% 3.50/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f25,plain,(
% 3.50/1.03    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.50/1.03    inference(ennf_transformation,[],[f9])).
% 3.50/1.03  
% 3.50/1.03  fof(f26,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.50/1.03    inference(flattening,[],[f25])).
% 3.50/1.03  
% 3.50/1.03  fof(f57,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f26])).
% 3.50/1.03  
% 3.50/1.03  fof(f65,plain,(
% 3.50/1.03    v1_funct_1(sK3)),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f10,axiom,(
% 3.50/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f27,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.03    inference(ennf_transformation,[],[f10])).
% 3.50/1.03  
% 3.50/1.03  fof(f58,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.03    inference(cnf_transformation,[],[f27])).
% 3.50/1.03  
% 3.50/1.03  fof(f13,axiom,(
% 3.50/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f30,plain,(
% 3.50/1.03    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.50/1.03    inference(ennf_transformation,[],[f13])).
% 3.50/1.03  
% 3.50/1.03  fof(f31,plain,(
% 3.50/1.03    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.50/1.03    inference(flattening,[],[f30])).
% 3.50/1.03  
% 3.50/1.03  fof(f61,plain,(
% 3.50/1.03    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f31])).
% 3.50/1.03  
% 3.50/1.03  fof(f66,plain,(
% 3.50/1.03    v1_funct_2(sK3,sK1,sK2)),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f1,axiom,(
% 3.50/1.03    v1_xboole_0(k1_xboole_0)),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f46,plain,(
% 3.50/1.03    v1_xboole_0(k1_xboole_0)),
% 3.50/1.03    inference(cnf_transformation,[],[f1])).
% 3.50/1.03  
% 3.50/1.03  fof(f64,plain,(
% 3.50/1.03    ~v1_xboole_0(sK2)),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f7,axiom,(
% 3.50/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f22,plain,(
% 3.50/1.03    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.50/1.03    inference(ennf_transformation,[],[f7])).
% 3.50/1.03  
% 3.50/1.03  fof(f55,plain,(
% 3.50/1.03    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f22])).
% 3.50/1.03  
% 3.50/1.03  fof(f71,plain,(
% 3.50/1.03    ~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f8,axiom,(
% 3.50/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f23,plain,(
% 3.50/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.50/1.03    inference(ennf_transformation,[],[f8])).
% 3.50/1.03  
% 3.50/1.03  fof(f24,plain,(
% 3.50/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.50/1.03    inference(flattening,[],[f23])).
% 3.50/1.03  
% 3.50/1.03  fof(f56,plain,(
% 3.50/1.03    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f24])).
% 3.50/1.03  
% 3.50/1.03  fof(f68,plain,(
% 3.50/1.03    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.50/1.03    inference(cnf_transformation,[],[f45])).
% 3.50/1.03  
% 3.50/1.03  fof(f4,axiom,(
% 3.50/1.03    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f52,plain,(
% 3.50/1.03    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.50/1.03    inference(cnf_transformation,[],[f4])).
% 3.50/1.03  
% 3.50/1.03  fof(f5,axiom,(
% 3.50/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f18,plain,(
% 3.50/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.50/1.03    inference(ennf_transformation,[],[f5])).
% 3.50/1.03  
% 3.50/1.03  fof(f19,plain,(
% 3.50/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.50/1.03    inference(flattening,[],[f18])).
% 3.50/1.03  
% 3.50/1.03  fof(f53,plain,(
% 3.50/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.50/1.03    inference(cnf_transformation,[],[f19])).
% 3.50/1.03  
% 3.50/1.03  fof(f3,axiom,(
% 3.50/1.03    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.50/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.03  
% 3.50/1.03  fof(f34,plain,(
% 3.50/1.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/1.03    inference(nnf_transformation,[],[f3])).
% 3.50/1.03  
% 3.50/1.03  fof(f35,plain,(
% 3.50/1.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/1.03    inference(rectify,[],[f34])).
% 3.50/1.03  
% 3.50/1.03  fof(f36,plain,(
% 3.50/1.03    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.50/1.03    introduced(choice_axiom,[])).
% 3.50/1.03  
% 3.50/1.03  fof(f37,plain,(
% 3.50/1.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.50/1.03  
% 3.50/1.03  fof(f48,plain,(
% 3.50/1.03    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.50/1.03    inference(cnf_transformation,[],[f37])).
% 3.50/1.03  
% 3.50/1.03  fof(f73,plain,(
% 3.50/1.03    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.50/1.03    inference(equality_resolution,[],[f48])).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1,plain,
% 3.50/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.50/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2303,plain,
% 3.50/1.03      ( r1_tarski(X0,X1)
% 3.50/1.03      | ~ r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,X1)))
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X1)),X1) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_4118,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,X0),X1)
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k10_relat_1(sK3,X1)))
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X1)),X1) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_2303]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_13501,plain,
% 3.50/1.03      ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
% 3.50/1.03      | r1_tarski(k9_relat_1(sK3,sK4),sK5) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_4118]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_8,plain,
% 3.50/1.03      ( ~ r1_tarski(X0,X1)
% 3.50/1.03      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.50/1.03      | ~ v1_relat_1(X2) ),
% 3.50/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2241,plain,
% 3.50/1.03      ( ~ r1_tarski(X0,X1)
% 3.50/1.03      | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3335,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,X0))
% 3.50/1.03      | ~ r1_tarski(sK4,X0)
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_2241]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_4974,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,sK4),k9_relat_1(sK3,k10_relat_1(sK3,sK5)))
% 3.50/1.03      | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5))
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_3335]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_4324,plain,
% 3.50/1.03      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.50/1.03      | ~ r1_tarski(sK4,X0)
% 3.50/1.03      | r1_tarski(sK4,k1_relat_1(sK3)) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_4326,plain,
% 3.50/1.03      ( ~ r1_tarski(sK1,k1_relat_1(sK3))
% 3.50/1.03      | r1_tarski(sK4,k1_relat_1(sK3))
% 3.50/1.03      | ~ r1_tarski(sK4,sK1) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_4324]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_21,negated_conjecture,
% 3.50/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.50/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1998,plain,
% 3.50/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_14,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.03      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.50/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2003,plain,
% 3.50/1.03      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.50/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2892,plain,
% 3.50/1.03      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.50/1.03      inference(superposition,[status(thm)],[c_1998,c_2003]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_18,negated_conjecture,
% 3.50/1.03      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 3.50/1.03      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 3.50/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2001,plain,
% 3.50/1.03      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 3.50/1.03      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3240,plain,
% 3.50/1.03      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 3.50/1.03      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 3.50/1.03      inference(demodulation,[status(thm)],[c_2892,c_2001]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_13,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.50/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2004,plain,
% 3.50/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.50/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2897,plain,
% 3.50/1.03      ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.50/1.03      inference(superposition,[status(thm)],[c_1998,c_2004]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3437,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 3.50/1.03      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 3.50/1.03      inference(demodulation,[status(thm)],[c_3240,c_2897]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_11,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.50/1.03      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.50/1.03      | ~ v1_funct_1(X1)
% 3.50/1.03      | ~ v1_relat_1(X1) ),
% 3.50/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_23,negated_conjecture,
% 3.50/1.03      ( v1_funct_1(sK3) ),
% 3.50/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_434,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.50/1.03      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.50/1.03      | ~ v1_relat_1(X1)
% 3.50/1.03      | sK3 != X1 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_435,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(sK3,X1))
% 3.50/1.03      | ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.50/1.03      | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(unflattening,[status(thm)],[c_434]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1994,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.50/1.03      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.50/1.03      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.50/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_30,plain,
% 3.50/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_436,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.50/1.03      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.50/1.03      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.50/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_12,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.03      | v1_relat_1(X0) ),
% 3.50/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2158,plain,
% 3.50/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.50/1.03      | v1_relat_1(sK3) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2159,plain,
% 3.50/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.50/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2664,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 3.50/1.03      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.50/1.03      | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
% 3.50/1.03      inference(global_propositional_subsumption,
% 3.50/1.03                [status(thm)],
% 3.50/1.03                [c_1994,c_30,c_436,c_2159]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2665,plain,
% 3.50/1.03      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 3.50/1.03      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.50/1.03      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
% 3.50/1.03      inference(renaming,[status(thm)],[c_2664]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3442,plain,
% 3.50/1.03      ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
% 3.50/1.03      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 3.50/1.03      inference(superposition,[status(thm)],[c_3437,c_2665]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3456,plain,
% 3.50/1.03      ( r1_tarski(sK4,k10_relat_1(sK3,sK5))
% 3.50/1.03      | ~ r1_tarski(sK4,k1_relat_1(sK3)) ),
% 3.50/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3442]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_16,plain,
% 3.50/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.03      | ~ v1_funct_1(X0)
% 3.50/1.03      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.50/1.03      | k1_xboole_0 = X2 ),
% 3.50/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_22,negated_conjecture,
% 3.50/1.03      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.50/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_409,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.03      | ~ v1_funct_1(X0)
% 3.50/1.03      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.50/1.03      | sK3 != X0
% 3.50/1.03      | sK2 != X2
% 3.50/1.03      | sK1 != X1
% 3.50/1.03      | k1_xboole_0 = X2 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_410,plain,
% 3.50/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.50/1.03      | ~ v1_funct_1(sK3)
% 3.50/1.03      | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
% 3.50/1.03      | k1_xboole_0 = sK2 ),
% 3.50/1.03      inference(unflattening,[status(thm)],[c_409]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_412,plain,
% 3.50/1.03      ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1 | k1_xboole_0 = sK2 ),
% 3.50/1.03      inference(global_propositional_subsumption,
% 3.50/1.03                [status(thm)],
% 3.50/1.03                [c_410,c_23,c_21]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3252,plain,
% 3.50/1.03      ( k10_relat_1(sK3,sK2) = sK1 | sK2 = k1_xboole_0 ),
% 3.50/1.03      inference(superposition,[status(thm)],[c_412,c_2892]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_0,plain,
% 3.50/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.50/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_24,negated_conjecture,
% 3.50/1.03      ( ~ v1_xboole_0(sK2) ),
% 3.50/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_351,plain,
% 3.50/1.03      ( sK2 != k1_xboole_0 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3418,plain,
% 3.50/1.03      ( k10_relat_1(sK3,sK2) = sK1 ),
% 3.50/1.03      inference(global_propositional_subsumption,
% 3.50/1.03                [status(thm)],
% 3.50/1.03                [c_3252,c_351]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_9,plain,
% 3.50/1.03      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.50/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2006,plain,
% 3.50/1.03      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.50/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3421,plain,
% 3.50/1.03      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 3.50/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.03      inference(superposition,[status(thm)],[c_3418,c_2006]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3433,plain,
% 3.50/1.03      ( r1_tarski(sK1,k1_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3421]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_17,negated_conjecture,
% 3.50/1.03      ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 3.50/1.03      | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 3.50/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2002,plain,
% 3.50/1.03      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 3.50/1.03      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
% 3.50/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3241,plain,
% 3.50/1.03      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 3.50/1.03      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 3.50/1.03      inference(demodulation,[status(thm)],[c_2892,c_2002]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3304,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 3.50/1.03      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 3.50/1.03      inference(demodulation,[status(thm)],[c_3241,c_2897]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_3307,plain,
% 3.50/1.03      ( ~ r1_tarski(k9_relat_1(sK3,sK4),sK5)
% 3.50/1.03      | ~ r1_tarski(sK4,k10_relat_1(sK3,sK5)) ),
% 3.50/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3304]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_10,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.50/1.03      | ~ v1_funct_1(X0)
% 3.50/1.03      | ~ v1_relat_1(X0) ),
% 3.50/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_422,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.50/1.03      | ~ v1_relat_1(X0)
% 3.50/1.03      | sK3 != X0 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_423,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0)
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(unflattening,[status(thm)],[c_422]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_2479,plain,
% 3.50/1.03      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,sK5)),sK5)
% 3.50/1.03      | ~ v1_relat_1(sK3) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_423]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1458,plain,( X0 = X0 ),theory(equality) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1483,plain,
% 3.50/1.03      ( sK1 = sK1 ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_1458]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1461,plain,
% 3.50/1.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.50/1.03      theory(equality) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1472,plain,
% 3.50/1.03      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_1461]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_20,negated_conjecture,
% 3.50/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.50/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_6,plain,
% 3.50/1.03      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.50/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_7,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.50/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_359,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_360,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/1.03      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.50/1.03      inference(unflattening,[status(thm)],[c_359]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_5,plain,
% 3.50/1.03      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_962,plain,
% 3.50/1.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.50/1.03      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_963,plain,
% 3.50/1.03      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/1.03      inference(renaming,[status(thm)],[c_962]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1015,plain,
% 3.50/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/1.03      inference(bin_hyper_res,[status(thm)],[c_360,c_963]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1259,plain,
% 3.50/1.03      ( r1_tarski(X0,X1)
% 3.50/1.03      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 3.50/1.03      | sK4 != X0 ),
% 3.50/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_1015]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1260,plain,
% 3.50/1.03      ( r1_tarski(sK4,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.50/1.03      inference(unflattening,[status(thm)],[c_1259]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(c_1262,plain,
% 3.50/1.03      ( r1_tarski(sK4,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 3.50/1.03      inference(instantiation,[status(thm)],[c_1260]) ).
% 3.50/1.03  
% 3.50/1.03  cnf(contradiction,plain,
% 3.50/1.03      ( $false ),
% 3.50/1.03      inference(minisat,
% 3.50/1.03                [status(thm)],
% 3.50/1.03                [c_13501,c_4974,c_4326,c_3456,c_3433,c_3307,c_2479,
% 3.50/1.03                 c_2158,c_1483,c_1472,c_1262,c_21]) ).
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.03  
% 3.50/1.03  ------                               Statistics
% 3.50/1.03  
% 3.50/1.03  ------ General
% 3.50/1.03  
% 3.50/1.03  abstr_ref_over_cycles:                  0
% 3.50/1.03  abstr_ref_under_cycles:                 0
% 3.50/1.03  gc_basic_clause_elim:                   0
% 3.50/1.03  forced_gc_time:                         0
% 3.50/1.03  parsing_time:                           0.007
% 3.50/1.03  unif_index_cands_time:                  0.
% 3.50/1.03  unif_index_add_time:                    0.
% 3.50/1.03  orderings_time:                         0.
% 3.50/1.03  out_proof_time:                         0.007
% 3.50/1.03  total_time:                             0.338
% 3.50/1.03  num_of_symbols:                         52
% 3.50/1.03  num_of_terms:                           13431
% 3.50/1.03  
% 3.50/1.03  ------ Preprocessing
% 3.50/1.03  
% 3.50/1.03  num_of_splits:                          0
% 3.50/1.03  num_of_split_atoms:                     0
% 3.50/1.03  num_of_reused_defs:                     0
% 3.50/1.03  num_eq_ax_congr_red:                    13
% 3.50/1.03  num_of_sem_filtered_clauses:            1
% 3.50/1.03  num_of_subtypes:                        0
% 3.50/1.03  monotx_restored_types:                  0
% 3.50/1.03  sat_num_of_epr_types:                   0
% 3.50/1.03  sat_num_of_non_cyclic_types:            0
% 3.50/1.03  sat_guarded_non_collapsed_types:        0
% 3.50/1.03  num_pure_diseq_elim:                    0
% 3.50/1.03  simp_replaced_by:                       0
% 3.50/1.03  res_preprocessed:                       125
% 3.50/1.03  prep_upred:                             0
% 3.50/1.03  prep_unflattend:                        74
% 3.50/1.03  smt_new_axioms:                         0
% 3.50/1.03  pred_elim_cands:                        4
% 3.50/1.03  pred_elim:                              3
% 3.50/1.03  pred_elim_cl:                           2
% 3.50/1.03  pred_elim_cycles:                       9
% 3.50/1.03  merged_defs:                            16
% 3.50/1.03  merged_defs_ncl:                        0
% 3.50/1.03  bin_hyper_res:                          17
% 3.50/1.03  prep_cycles:                            4
% 3.50/1.03  pred_elim_time:                         0.018
% 3.50/1.03  splitting_time:                         0.
% 3.50/1.03  sem_filter_time:                        0.
% 3.50/1.03  monotx_time:                            0.
% 3.50/1.03  subtype_inf_time:                       0.
% 3.50/1.03  
% 3.50/1.03  ------ Problem properties
% 3.50/1.03  
% 3.50/1.03  clauses:                                24
% 3.50/1.03  conjectures:                            5
% 3.50/1.03  epr:                                    5
% 3.50/1.03  horn:                                   21
% 3.50/1.03  ground:                                 8
% 3.50/1.03  unary:                                  6
% 3.50/1.03  binary:                                 13
% 3.50/1.03  lits:                                   48
% 3.50/1.03  lits_eq:                                9
% 3.50/1.03  fd_pure:                                0
% 3.50/1.03  fd_pseudo:                              0
% 3.50/1.03  fd_cond:                                0
% 3.50/1.03  fd_pseudo_cond:                         2
% 3.50/1.03  ac_symbols:                             0
% 3.50/1.03  
% 3.50/1.03  ------ Propositional Solver
% 3.50/1.03  
% 3.50/1.03  prop_solver_calls:                      27
% 3.50/1.03  prop_fast_solver_calls:                 1007
% 3.50/1.03  smt_solver_calls:                       0
% 3.50/1.03  smt_fast_solver_calls:                  0
% 3.50/1.03  prop_num_of_clauses:                    4914
% 3.50/1.03  prop_preprocess_simplified:             9907
% 3.50/1.03  prop_fo_subsumed:                       18
% 3.50/1.03  prop_solver_time:                       0.
% 3.50/1.03  smt_solver_time:                        0.
% 3.50/1.03  smt_fast_solver_time:                   0.
% 3.50/1.03  prop_fast_solver_time:                  0.
% 3.50/1.03  prop_unsat_core_time:                   0.
% 3.50/1.03  
% 3.50/1.03  ------ QBF
% 3.50/1.03  
% 3.50/1.03  qbf_q_res:                              0
% 3.50/1.03  qbf_num_tautologies:                    0
% 3.50/1.03  qbf_prep_cycles:                        0
% 3.50/1.03  
% 3.50/1.03  ------ BMC1
% 3.50/1.03  
% 3.50/1.03  bmc1_current_bound:                     -1
% 3.50/1.03  bmc1_last_solved_bound:                 -1
% 3.50/1.03  bmc1_unsat_core_size:                   -1
% 3.50/1.03  bmc1_unsat_core_parents_size:           -1
% 3.50/1.03  bmc1_merge_next_fun:                    0
% 3.50/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.50/1.03  
% 3.50/1.03  ------ Instantiation
% 3.50/1.03  
% 3.50/1.03  inst_num_of_clauses:                    1317
% 3.50/1.03  inst_num_in_passive:                    168
% 3.50/1.03  inst_num_in_active:                     502
% 3.50/1.03  inst_num_in_unprocessed:                646
% 3.50/1.03  inst_num_of_loops:                      545
% 3.50/1.03  inst_num_of_learning_restarts:          0
% 3.50/1.03  inst_num_moves_active_passive:          40
% 3.50/1.03  inst_lit_activity:                      0
% 3.50/1.03  inst_lit_activity_moves:                0
% 3.50/1.03  inst_num_tautologies:                   0
% 3.50/1.03  inst_num_prop_implied:                  0
% 3.50/1.03  inst_num_existing_simplified:           0
% 3.50/1.03  inst_num_eq_res_simplified:             0
% 3.50/1.03  inst_num_child_elim:                    0
% 3.50/1.03  inst_num_of_dismatching_blockings:      1595
% 3.50/1.03  inst_num_of_non_proper_insts:           1170
% 3.50/1.03  inst_num_of_duplicates:                 0
% 3.50/1.03  inst_inst_num_from_inst_to_res:         0
% 3.50/1.03  inst_dismatching_checking_time:         0.
% 3.50/1.03  
% 3.50/1.03  ------ Resolution
% 3.50/1.03  
% 3.50/1.03  res_num_of_clauses:                     0
% 3.50/1.03  res_num_in_passive:                     0
% 3.50/1.03  res_num_in_active:                      0
% 3.50/1.03  res_num_of_loops:                       129
% 3.50/1.03  res_forward_subset_subsumed:            30
% 3.50/1.03  res_backward_subset_subsumed:           0
% 3.50/1.03  res_forward_subsumed:                   0
% 3.50/1.03  res_backward_subsumed:                  0
% 3.50/1.03  res_forward_subsumption_resolution:     0
% 3.50/1.03  res_backward_subsumption_resolution:    0
% 3.50/1.03  res_clause_to_clause_subsumption:       1198
% 3.50/1.03  res_orphan_elimination:                 0
% 3.50/1.03  res_tautology_del:                      112
% 3.50/1.03  res_num_eq_res_simplified:              0
% 3.50/1.03  res_num_sel_changes:                    0
% 3.50/1.03  res_moves_from_active_to_pass:          0
% 3.50/1.03  
% 3.50/1.03  ------ Superposition
% 3.50/1.03  
% 3.50/1.03  sup_time_total:                         0.
% 3.50/1.03  sup_time_generating:                    0.
% 3.50/1.03  sup_time_sim_full:                      0.
% 3.50/1.03  sup_time_sim_immed:                     0.
% 3.50/1.03  
% 3.50/1.03  sup_num_of_clauses:                     280
% 3.50/1.03  sup_num_in_active:                      105
% 3.50/1.03  sup_num_in_passive:                     175
% 3.50/1.03  sup_num_of_loops:                       108
% 3.50/1.03  sup_fw_superposition:                   182
% 3.50/1.03  sup_bw_superposition:                   175
% 3.50/1.03  sup_immediate_simplified:               26
% 3.50/1.03  sup_given_eliminated:                   0
% 3.50/1.03  comparisons_done:                       0
% 3.50/1.03  comparisons_avoided:                    0
% 3.50/1.03  
% 3.50/1.03  ------ Simplifications
% 3.50/1.03  
% 3.50/1.03  
% 3.50/1.03  sim_fw_subset_subsumed:                 14
% 3.50/1.03  sim_bw_subset_subsumed:                 4
% 3.50/1.03  sim_fw_subsumed:                        9
% 3.50/1.03  sim_bw_subsumed:                        0
% 3.50/1.03  sim_fw_subsumption_res:                 0
% 3.50/1.03  sim_bw_subsumption_res:                 0
% 3.50/1.03  sim_tautology_del:                      57
% 3.50/1.03  sim_eq_tautology_del:                   1
% 3.50/1.03  sim_eq_res_simp:                        0
% 3.50/1.03  sim_fw_demodulated:                     3
% 3.50/1.03  sim_bw_demodulated:                     2
% 3.50/1.03  sim_light_normalised:                   4
% 3.50/1.03  sim_joinable_taut:                      0
% 3.50/1.03  sim_joinable_simp:                      0
% 3.50/1.03  sim_ac_normalised:                      0
% 3.50/1.03  sim_smt_subsumption:                    0
% 3.50/1.03  
%------------------------------------------------------------------------------
