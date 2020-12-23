%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:07 EST 2020

% Result     : Theorem 19.73s
% Output     : CNFRefutation 19.73s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 323 expanded)
%              Number of clauses        :   62 (  82 expanded)
%              Number of leaves         :   19 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  423 (2581 expanded)
%              Number of equality atoms :   86 ( 106 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

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
    inference(ennf_transformation,[],[f30])).

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

fof(f71,plain,(
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

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,sK6))
          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),sK6) )
        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,sK6))
          | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK6) )
        & m1_subset_1(sK6,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
            ( ( ~ r1_tarski(sK5,k8_relset_1(X0,X1,X2,X4))
              | ~ r1_tarski(k7_relset_1(X0,X1,X2,sK5),X4) )
            & ( r1_tarski(sK5,k8_relset_1(X0,X1,X2,X4))
              | r1_tarski(k7_relset_1(X0,X1,X2,sK5),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
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
                ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,sK4,X4))
                  | ~ r1_tarski(k7_relset_1(X0,X1,sK4,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(X0,X1,sK4,X4))
                  | r1_tarski(k7_relset_1(X0,X1,sK4,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(X1)) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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
                    ( ( ~ r1_tarski(X3,k8_relset_1(X0,sK3,X2,X4))
                      | ~ r1_tarski(k7_relset_1(X0,sK3,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(X0,sK3,X2,X4))
                      | r1_tarski(k7_relset_1(X0,sK3,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(sK3)) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
            & v1_funct_2(X2,X0,sK3)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
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
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK2,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK2,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK2,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK2,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
              & v1_funct_2(X2,sK2,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( ~ r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6))
      | ~ r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) )
    & ( r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6))
      | r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f72,f77,f76,f75,f74,f73])).

fof(f121,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f124,plain,
    ( r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6))
    | r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f78])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f119,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f120,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f125,plain,
    ( ~ r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6))
    | ~ r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f78])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f78])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3740,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK6)
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7749,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(k9_relat_1(sK4,X1),X0)
    | r1_tarski(k9_relat_1(sK4,X1),sK6) ),
    inference(instantiation,[status(thm)],[c_3740])).

cnf(c_22718,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
    | ~ r1_tarski(k9_relat_1(sK4,X1),sK6)
    | r1_tarski(k9_relat_1(sK4,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_7749])).

cnf(c_54443,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
    | r1_tarski(k9_relat_1(sK4,X0),sK6)
    | ~ r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_22718])).

cnf(c_100149,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6)
    | ~ r1_tarski(k9_relat_1(sK4,sK5),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
    | r1_tarski(k9_relat_1(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_54443])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2268,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_38694,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK4,sK6))
    | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_93021,plain,
    ( r1_tarski(k9_relat_1(sK4,sK5),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
    | ~ r1_tarski(sK5,k10_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_38694])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1672,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1682,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10328,plain,
    ( k7_relset_1(sK2,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1672,c_1682])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1681,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8942,plain,
    ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1672,c_1681])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)
    | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1675,plain,
    ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) = iProver_top
    | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9315,plain,
    ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) = iProver_top
    | r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8942,c_1675])).

cnf(c_11659,plain,
    ( r1_tarski(k9_relat_1(sK4,sK5),sK6) = iProver_top
    | r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10328,c_9315])).

cnf(c_28,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1686,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13345,plain,
    ( r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top
    | r1_tarski(sK5,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11659,c_1686])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1683,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8975,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1672,c_1683])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1680,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6562,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) = k1_relset_1(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1672,c_1680])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1677,plain,
    ( k8_relset_1(X0,X1,X2,X1) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3795,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1677])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_50,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_762,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2065,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2067,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_4684,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_45,c_49,c_50,c_4,c_2067])).

cnf(c_6574,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6562,c_4684])).

cnf(c_8987,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8975,c_6574])).

cnf(c_13350,plain,
    ( r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top
    | r1_tarski(sK5,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13345,c_8987])).

cnf(c_13367,plain,
    ( r1_tarski(sK5,k10_relat_1(sK4,sK6))
    | ~ r1_tarski(sK5,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13350])).

cnf(c_38,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)
    | ~ r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1676,plain,
    ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) != iProver_top
    | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9316,plain,
    ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) != iProver_top
    | r1_tarski(sK5,k10_relat_1(sK4,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8942,c_1676])).

cnf(c_11660,plain,
    ( r1_tarski(k9_relat_1(sK4,sK5),sK6) != iProver_top
    | r1_tarski(sK5,k10_relat_1(sK4,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10328,c_9316])).

cnf(c_11673,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK5),sK6)
    | ~ r1_tarski(sK5,k10_relat_1(sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11660])).

cnf(c_27,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2149,plain,
    ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,X0)),X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3763,plain,
    ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2329,plain,
    ( r1_tarski(sK5,sK2) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2062,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100149,c_93021,c_13367,c_11673,c_3763,c_2329,c_2062,c_42,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:25:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.73/2.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.73/2.97  
% 19.73/2.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.73/2.97  
% 19.73/2.97  ------  iProver source info
% 19.73/2.97  
% 19.73/2.97  git: date: 2020-06-30 10:37:57 +0100
% 19.73/2.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.73/2.97  git: non_committed_changes: false
% 19.73/2.97  git: last_make_outside_of_git: false
% 19.73/2.97  
% 19.73/2.97  ------ 
% 19.73/2.97  ------ Parsing...
% 19.73/2.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.73/2.97  
% 19.73/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.73/2.97  
% 19.73/2.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.73/2.97  
% 19.73/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.73/2.97  ------ Proving...
% 19.73/2.97  ------ Problem Properties 
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  clauses                                 46
% 19.73/2.97  conjectures                             9
% 19.73/2.97  EPR                                     13
% 19.73/2.97  Horn                                    41
% 19.73/2.97  unary                                   16
% 19.73/2.97  binary                                  17
% 19.73/2.97  lits                                    94
% 19.73/2.97  lits eq                                 17
% 19.73/2.97  fd_pure                                 0
% 19.73/2.97  fd_pseudo                               0
% 19.73/2.97  fd_cond                                 2
% 19.73/2.97  fd_pseudo_cond                          1
% 19.73/2.97  AC symbols                              0
% 19.73/2.97  
% 19.73/2.97  ------ Input Options Time Limit: Unbounded
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  ------ 
% 19.73/2.97  Current options:
% 19.73/2.97  ------ 
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  ------ Proving...
% 19.73/2.97  
% 19.73/2.97  
% 19.73/2.97  % SZS status Theorem for theBenchmark.p
% 19.73/2.97  
% 19.73/2.97  % SZS output start CNFRefutation for theBenchmark.p
% 19.73/2.97  
% 19.73/2.97  fof(f7,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f35,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.73/2.97    inference(ennf_transformation,[],[f7])).
% 19.73/2.97  
% 19.73/2.97  fof(f36,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.73/2.97    inference(flattening,[],[f35])).
% 19.73/2.97  
% 19.73/2.97  fof(f89,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.73/2.97    inference(cnf_transformation,[],[f36])).
% 19.73/2.97  
% 19.73/2.97  fof(f18,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f42,plain,(
% 19.73/2.97    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 19.73/2.97    inference(ennf_transformation,[],[f18])).
% 19.73/2.97  
% 19.73/2.97  fof(f43,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 19.73/2.97    inference(flattening,[],[f42])).
% 19.73/2.97  
% 19.73/2.97  fof(f104,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 19.73/2.97    inference(cnf_transformation,[],[f43])).
% 19.73/2.97  
% 19.73/2.97  fof(f29,conjecture,(
% 19.73/2.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f30,negated_conjecture,(
% 19.73/2.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 19.73/2.97    inference(negated_conjecture,[],[f29])).
% 19.73/2.97  
% 19.73/2.97  fof(f57,plain,(
% 19.73/2.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.73/2.97    inference(ennf_transformation,[],[f30])).
% 19.73/2.97  
% 19.73/2.97  fof(f58,plain,(
% 19.73/2.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.73/2.97    inference(flattening,[],[f57])).
% 19.73/2.97  
% 19.73/2.97  fof(f71,plain,(
% 19.73/2.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.73/2.97    inference(nnf_transformation,[],[f58])).
% 19.73/2.97  
% 19.73/2.97  fof(f72,plain,(
% 19.73/2.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.73/2.97    inference(flattening,[],[f71])).
% 19.73/2.97  
% 19.73/2.97  fof(f77,plain,(
% 19.73/2.97    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK6)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK6)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK6)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK6)) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 19.73/2.97    introduced(choice_axiom,[])).
% 19.73/2.97  
% 19.73/2.97  fof(f76,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK5,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK5),X4)) & (r1_tarski(sK5,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK5),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK5,k1_zfmisc_1(X0)))) )),
% 19.73/2.97    introduced(choice_axiom,[])).
% 19.73/2.97  
% 19.73/2.97  fof(f75,plain,(
% 19.73/2.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK4,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK4,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK4,X4)) | r1_tarski(k7_relset_1(X0,X1,sK4,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 19.73/2.97    introduced(choice_axiom,[])).
% 19.73/2.97  
% 19.73/2.97  fof(f74,plain,(
% 19.73/2.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK3,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK3,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK3,X2,X4)) | r1_tarski(k7_relset_1(X0,sK3,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK3))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) & v1_funct_2(X2,X0,sK3) & v1_funct_1(X2)) & ~v1_xboole_0(sK3))) )),
% 19.73/2.97    introduced(choice_axiom,[])).
% 19.73/2.97  
% 19.73/2.97  fof(f73,plain,(
% 19.73/2.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK2,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK2,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK2,X1,X2,X4)) | r1_tarski(k7_relset_1(sK2,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X2,sK2,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 19.73/2.97    introduced(choice_axiom,[])).
% 19.73/2.97  
% 19.73/2.97  fof(f78,plain,(
% 19.73/2.97    (((((~r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) | ~r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)) & (r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) | r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 19.73/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f72,f77,f76,f75,f74,f73])).
% 19.73/2.97  
% 19.73/2.97  fof(f121,plain,(
% 19.73/2.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f25,axiom,(
% 19.73/2.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f52,plain,(
% 19.73/2.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.73/2.97    inference(ennf_transformation,[],[f25])).
% 19.73/2.97  
% 19.73/2.97  fof(f111,plain,(
% 19.73/2.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f52])).
% 19.73/2.97  
% 19.73/2.97  fof(f26,axiom,(
% 19.73/2.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f53,plain,(
% 19.73/2.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.73/2.97    inference(ennf_transformation,[],[f26])).
% 19.73/2.97  
% 19.73/2.97  fof(f112,plain,(
% 19.73/2.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f53])).
% 19.73/2.97  
% 19.73/2.97  fof(f124,plain,(
% 19.73/2.97    r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) | r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f21,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f47,plain,(
% 19.73/2.97    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.73/2.97    inference(ennf_transformation,[],[f21])).
% 19.73/2.97  
% 19.73/2.97  fof(f48,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.73/2.97    inference(flattening,[],[f47])).
% 19.73/2.97  
% 19.73/2.97  fof(f107,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.73/2.97    inference(cnf_transformation,[],[f48])).
% 19.73/2.97  
% 19.73/2.97  fof(f24,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f51,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.73/2.97    inference(ennf_transformation,[],[f24])).
% 19.73/2.97  
% 19.73/2.97  fof(f110,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f51])).
% 19.73/2.97  
% 19.73/2.97  fof(f27,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f54,plain,(
% 19.73/2.97    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.73/2.97    inference(ennf_transformation,[],[f27])).
% 19.73/2.97  
% 19.73/2.97  fof(f114,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f54])).
% 19.73/2.97  
% 19.73/2.97  fof(f28,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f55,plain,(
% 19.73/2.97    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.73/2.97    inference(ennf_transformation,[],[f28])).
% 19.73/2.97  
% 19.73/2.97  fof(f56,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.73/2.97    inference(flattening,[],[f55])).
% 19.73/2.97  
% 19.73/2.97  fof(f115,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.73/2.97    inference(cnf_transformation,[],[f56])).
% 19.73/2.97  
% 19.73/2.97  fof(f118,plain,(
% 19.73/2.97    ~v1_xboole_0(sK3)),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f119,plain,(
% 19.73/2.97    v1_funct_1(sK4)),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f120,plain,(
% 19.73/2.97    v1_funct_2(sK4,sK2,sK3)),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f3,axiom,(
% 19.73/2.97    v1_xboole_0(k1_xboole_0)),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f83,plain,(
% 19.73/2.97    v1_xboole_0(k1_xboole_0)),
% 19.73/2.97    inference(cnf_transformation,[],[f3])).
% 19.73/2.97  
% 19.73/2.97  fof(f125,plain,(
% 19.73/2.97    ~r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) | ~r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f20,axiom,(
% 19.73/2.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f45,plain,(
% 19.73/2.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.73/2.97    inference(ennf_transformation,[],[f20])).
% 19.73/2.97  
% 19.73/2.97  fof(f46,plain,(
% 19.73/2.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.73/2.97    inference(flattening,[],[f45])).
% 19.73/2.97  
% 19.73/2.97  fof(f106,plain,(
% 19.73/2.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.73/2.97    inference(cnf_transformation,[],[f46])).
% 19.73/2.97  
% 19.73/2.97  fof(f14,axiom,(
% 19.73/2.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f69,plain,(
% 19.73/2.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.73/2.97    inference(nnf_transformation,[],[f14])).
% 19.73/2.97  
% 19.73/2.97  fof(f98,plain,(
% 19.73/2.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f69])).
% 19.73/2.97  
% 19.73/2.97  fof(f122,plain,(
% 19.73/2.97    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 19.73/2.97    inference(cnf_transformation,[],[f78])).
% 19.73/2.97  
% 19.73/2.97  fof(f22,axiom,(
% 19.73/2.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.73/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.73/2.97  
% 19.73/2.97  fof(f49,plain,(
% 19.73/2.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.73/2.97    inference(ennf_transformation,[],[f22])).
% 19.73/2.97  
% 19.73/2.97  fof(f108,plain,(
% 19.73/2.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.73/2.97    inference(cnf_transformation,[],[f49])).
% 19.73/2.97  
% 19.73/2.97  cnf(c_10,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.73/2.97      inference(cnf_transformation,[],[f89]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_3740,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK6) | r1_tarski(X0,sK6) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_10]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_7749,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,sK6)
% 19.73/2.97      | ~ r1_tarski(k9_relat_1(sK4,X1),X0)
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,X1),sK6) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_3740]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_22718,plain,
% 19.73/2.97      ( ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
% 19.73/2.97      | ~ r1_tarski(k9_relat_1(sK4,X1),sK6)
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,X0),sK6) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_7749]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_54443,plain,
% 19.73/2.97      ( ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,X0),sK6)
% 19.73/2.97      | ~ r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_22718]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_100149,plain,
% 19.73/2.97      ( ~ r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6)
% 19.73/2.97      | ~ r1_tarski(k9_relat_1(sK4,sK5),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,sK5),sK6) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_54443]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_25,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,X1)
% 19.73/2.97      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 19.73/2.97      | ~ v1_relat_1(X2) ),
% 19.73/2.97      inference(cnf_transformation,[],[f104]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_2268,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,X1)
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
% 19.73/2.97      | ~ v1_relat_1(sK4) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_25]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_38694,plain,
% 19.73/2.97      ( ~ r1_tarski(X0,k10_relat_1(sK4,sK6))
% 19.73/2.97      | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
% 19.73/2.97      | ~ v1_relat_1(sK4) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_2268]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_93021,plain,
% 19.73/2.97      ( r1_tarski(k9_relat_1(sK4,sK5),k9_relat_1(sK4,k10_relat_1(sK4,sK6)))
% 19.73/2.97      | ~ r1_tarski(sK5,k10_relat_1(sK4,sK6))
% 19.73/2.97      | ~ v1_relat_1(sK4) ),
% 19.73/2.97      inference(instantiation,[status(thm)],[c_38694]) ).
% 19.73/2.97  
% 19.73/2.97  cnf(c_42,negated_conjecture,
% 19.73/2.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 19.73/2.97      inference(cnf_transformation,[],[f121]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1672,plain,
% 19.73/2.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_32,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 19.73/2.98      inference(cnf_transformation,[],[f111]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1682,plain,
% 19.73/2.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 19.73/2.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_10328,plain,
% 19.73/2.98      ( k7_relset_1(sK2,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_1672,c_1682]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_33,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 19.73/2.98      inference(cnf_transformation,[],[f112]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1681,plain,
% 19.73/2.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 19.73/2.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_8942,plain,
% 19.73/2.98      ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_1672,c_1681]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_39,negated_conjecture,
% 19.73/2.98      ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)
% 19.73/2.98      | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) ),
% 19.73/2.98      inference(cnf_transformation,[],[f124]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1675,plain,
% 19.73/2.98      ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) = iProver_top
% 19.73/2.98      | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_9315,plain,
% 19.73/2.98      ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) = iProver_top
% 19.73/2.98      | r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top ),
% 19.73/2.98      inference(demodulation,[status(thm)],[c_8942,c_1675]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_11659,plain,
% 19.73/2.98      ( r1_tarski(k9_relat_1(sK4,sK5),sK6) = iProver_top
% 19.73/2.98      | r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top ),
% 19.73/2.98      inference(demodulation,[status(thm)],[c_10328,c_9315]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_28,plain,
% 19.73/2.98      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 19.73/2.98      | ~ r1_tarski(X0,k1_relat_1(X1))
% 19.73/2.98      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 19.73/2.98      | ~ v1_funct_1(X1)
% 19.73/2.98      | ~ v1_relat_1(X1) ),
% 19.73/2.98      inference(cnf_transformation,[],[f107]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1686,plain,
% 19.73/2.98      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 19.73/2.98      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 19.73/2.98      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 19.73/2.98      | v1_funct_1(X1) != iProver_top
% 19.73/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_13345,plain,
% 19.73/2.98      ( r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top
% 19.73/2.98      | r1_tarski(sK5,k1_relat_1(sK4)) != iProver_top
% 19.73/2.98      | v1_funct_1(sK4) != iProver_top
% 19.73/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_11659,c_1686]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_31,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.73/2.98      inference(cnf_transformation,[],[f110]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1683,plain,
% 19.73/2.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.73/2.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_8975,plain,
% 19.73/2.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_1672,c_1683]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_34,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 19.73/2.98      inference(cnf_transformation,[],[f114]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1680,plain,
% 19.73/2.98      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 19.73/2.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_6562,plain,
% 19.73/2.98      ( k8_relset_1(sK2,sK3,sK4,sK3) = k1_relset_1(sK2,sK3,sK4) ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_1672,c_1680]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_37,plain,
% 19.73/2.98      ( ~ v1_funct_2(X0,X1,X2)
% 19.73/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | ~ v1_funct_1(X0)
% 19.73/2.98      | k8_relset_1(X1,X2,X0,X2) = X1
% 19.73/2.98      | k1_xboole_0 = X2 ),
% 19.73/2.98      inference(cnf_transformation,[],[f115]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1677,plain,
% 19.73/2.98      ( k8_relset_1(X0,X1,X2,X1) = X0
% 19.73/2.98      | k1_xboole_0 = X1
% 19.73/2.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.73/2.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.73/2.98      | v1_funct_1(X2) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_3795,plain,
% 19.73/2.98      ( k8_relset_1(sK2,sK3,sK4,sK3) = sK2
% 19.73/2.98      | sK3 = k1_xboole_0
% 19.73/2.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 19.73/2.98      | v1_funct_1(sK4) != iProver_top ),
% 19.73/2.98      inference(superposition,[status(thm)],[c_1672,c_1677]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_45,negated_conjecture,
% 19.73/2.98      ( ~ v1_xboole_0(sK3) ),
% 19.73/2.98      inference(cnf_transformation,[],[f118]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_44,negated_conjecture,
% 19.73/2.98      ( v1_funct_1(sK4) ),
% 19.73/2.98      inference(cnf_transformation,[],[f119]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_49,plain,
% 19.73/2.98      ( v1_funct_1(sK4) = iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_43,negated_conjecture,
% 19.73/2.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 19.73/2.98      inference(cnf_transformation,[],[f120]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_50,plain,
% 19.73/2.98      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_4,plain,
% 19.73/2.98      ( v1_xboole_0(k1_xboole_0) ),
% 19.73/2.98      inference(cnf_transformation,[],[f83]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_762,plain,
% 19.73/2.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.73/2.98      theory(equality) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_2065,plain,
% 19.73/2.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 19.73/2.98      inference(instantiation,[status(thm)],[c_762]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_2067,plain,
% 19.73/2.98      ( v1_xboole_0(sK3)
% 19.73/2.98      | ~ v1_xboole_0(k1_xboole_0)
% 19.73/2.98      | sK3 != k1_xboole_0 ),
% 19.73/2.98      inference(instantiation,[status(thm)],[c_2065]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_4684,plain,
% 19.73/2.98      ( k8_relset_1(sK2,sK3,sK4,sK3) = sK2 ),
% 19.73/2.98      inference(global_propositional_subsumption,
% 19.73/2.98                [status(thm)],
% 19.73/2.98                [c_3795,c_45,c_49,c_50,c_4,c_2067]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_6574,plain,
% 19.73/2.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 ),
% 19.73/2.98      inference(light_normalisation,[status(thm)],[c_6562,c_4684]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_8987,plain,
% 19.73/2.98      ( k1_relat_1(sK4) = sK2 ),
% 19.73/2.98      inference(light_normalisation,[status(thm)],[c_8975,c_6574]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_13350,plain,
% 19.73/2.98      ( r1_tarski(sK5,k10_relat_1(sK4,sK6)) = iProver_top
% 19.73/2.98      | r1_tarski(sK5,sK2) != iProver_top
% 19.73/2.98      | v1_funct_1(sK4) != iProver_top
% 19.73/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.73/2.98      inference(light_normalisation,[status(thm)],[c_13345,c_8987]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_13367,plain,
% 19.73/2.98      ( r1_tarski(sK5,k10_relat_1(sK4,sK6))
% 19.73/2.98      | ~ r1_tarski(sK5,sK2)
% 19.73/2.98      | ~ v1_funct_1(sK4)
% 19.73/2.98      | ~ v1_relat_1(sK4) ),
% 19.73/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_13350]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_38,negated_conjecture,
% 19.73/2.98      ( ~ r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6)
% 19.73/2.98      | ~ r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) ),
% 19.73/2.98      inference(cnf_transformation,[],[f125]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_1676,plain,
% 19.73/2.98      ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) != iProver_top
% 19.73/2.98      | r1_tarski(sK5,k8_relset_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 19.73/2.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_9316,plain,
% 19.73/2.98      ( r1_tarski(k7_relset_1(sK2,sK3,sK4,sK5),sK6) != iProver_top
% 19.73/2.98      | r1_tarski(sK5,k10_relat_1(sK4,sK6)) != iProver_top ),
% 19.73/2.98      inference(demodulation,[status(thm)],[c_8942,c_1676]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_11660,plain,
% 19.73/2.98      ( r1_tarski(k9_relat_1(sK4,sK5),sK6) != iProver_top
% 19.73/2.98      | r1_tarski(sK5,k10_relat_1(sK4,sK6)) != iProver_top ),
% 19.73/2.98      inference(demodulation,[status(thm)],[c_10328,c_9316]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_11673,plain,
% 19.73/2.98      ( ~ r1_tarski(k9_relat_1(sK4,sK5),sK6)
% 19.73/2.98      | ~ r1_tarski(sK5,k10_relat_1(sK4,sK6)) ),
% 19.73/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_11660]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_27,plain,
% 19.73/2.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 19.73/2.98      | ~ v1_funct_1(X0)
% 19.73/2.98      | ~ v1_relat_1(X0) ),
% 19.73/2.98      inference(cnf_transformation,[],[f106]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_2149,plain,
% 19.73/2.98      ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,X0)),X0)
% 19.73/2.98      | ~ v1_funct_1(sK4)
% 19.73/2.98      | ~ v1_relat_1(sK4) ),
% 19.73/2.98      inference(instantiation,[status(thm)],[c_27]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_3763,plain,
% 19.73/2.98      ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,sK6)),sK6)
% 19.73/2.98      | ~ v1_funct_1(sK4)
% 19.73/2.98      | ~ v1_relat_1(sK4) ),
% 19.73/2.98      inference(instantiation,[status(thm)],[c_2149]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_20,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.73/2.98      inference(cnf_transformation,[],[f98]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_41,negated_conjecture,
% 19.73/2.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 19.73/2.98      inference(cnf_transformation,[],[f122]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_2329,plain,
% 19.73/2.98      ( r1_tarski(sK5,sK2) ),
% 19.73/2.98      inference(resolution,[status(thm)],[c_20,c_41]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_29,plain,
% 19.73/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.73/2.98      | v1_relat_1(X0) ),
% 19.73/2.98      inference(cnf_transformation,[],[f108]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(c_2062,plain,
% 19.73/2.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.73/2.98      | v1_relat_1(sK4) ),
% 19.73/2.98      inference(instantiation,[status(thm)],[c_29]) ).
% 19.73/2.98  
% 19.73/2.98  cnf(contradiction,plain,
% 19.73/2.98      ( $false ),
% 19.73/2.98      inference(minisat,
% 19.73/2.98                [status(thm)],
% 19.73/2.98                [c_100149,c_93021,c_13367,c_11673,c_3763,c_2329,c_2062,
% 19.73/2.98                 c_42,c_44]) ).
% 19.73/2.98  
% 19.73/2.98  
% 19.73/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.73/2.98  
% 19.73/2.98  ------                               Statistics
% 19.73/2.98  
% 19.73/2.98  ------ Selected
% 19.73/2.98  
% 19.73/2.98  total_time:                             2.417
% 19.73/2.98  
%------------------------------------------------------------------------------
