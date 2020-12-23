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
% DateTime   : Thu Dec  3 12:09:58 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 399 expanded)
%              Number of clauses        :   73 ( 110 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   17
%              Number of atoms          :  403 (2228 expanded)
%              Number of equality atoms :  114 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(k3_funct_2(X0,X1,sK3,X2),k2_relset_1(X0,X1,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r2_hidden(k3_funct_2(X0,X1,X3,sK2),k2_relset_1(X0,X1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k3_funct_2(X0,sK1,X3,X2),k2_relset_1(X0,sK1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
                & v1_funct_2(X3,X0,sK1)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,X0) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                  & v1_funct_2(X3,sK0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f62,f61,f60,f59])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f105,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f108,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3112,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7497,plain,
    ( k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = k1_relset_1(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_3109,c_3112])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3117,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4603,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3109,c_3117])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3113,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6650,plain,
    ( k7_relset_1(sK0,sK1,sK3,sK0) = k2_relset_1(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_3109,c_3113])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3116,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4324,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3109,c_3116])).

cnf(c_6652,plain,
    ( k7_relset_1(sK0,sK1,sK3,sK0) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_6650,c_4324])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3115,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5542,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3109,c_3115])).

cnf(c_6936,plain,
    ( k9_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5542,c_6652])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_40])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_540,plain,
    ( k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_41,c_39])).

cnf(c_6067,plain,
    ( k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5542,c_540])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_132,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_135,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_139,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2256,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3426,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_3428,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3426])).

cnf(c_6259,plain,
    ( k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6067,c_43,c_132,c_135,c_139,c_3428])).

cnf(c_6939,plain,
    ( k8_relset_1(sK0,sK1,sK3,k2_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_6936,c_6259])).

cnf(c_7499,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_7497,c_4603,c_6652,c_6939])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_41])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_3102,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3108,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK1 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_40])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,sK0)
    | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_44,c_41,c_39])).

cnf(c_3104,plain,
    ( k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_3526,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_3108,c_3104])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3110,plain,
    ( r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3528,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3526,c_3110])).

cnf(c_4326,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4324,c_3528])).

cnf(c_4461,plain,
    ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_4326])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_3661,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3762,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3763,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3762])).

cnf(c_4464,plain,
    ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4461,c_50,c_3661,c_3763])).

cnf(c_7822,plain,
    ( r2_hidden(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7499,c_4464])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_898,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_42])).

cnf(c_899,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_900,plain,
    ( r2_hidden(sK2,sK0) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_45,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7822,c_900,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.00  
% 3.16/1.00  ------  iProver source info
% 3.16/1.00  
% 3.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.00  git: non_committed_changes: false
% 3.16/1.00  git: last_make_outside_of_git: false
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     num_symb
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       true
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  ------ Parsing...
% 3.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.00  ------ Proving...
% 3.16/1.00  ------ Problem Properties 
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  clauses                                 42
% 3.16/1.00  conjectures                             5
% 3.16/1.00  EPR                                     12
% 3.16/1.00  Horn                                    39
% 3.16/1.00  unary                                   13
% 3.16/1.00  binary                                  15
% 3.16/1.00  lits                                    86
% 3.16/1.00  lits eq                                 27
% 3.16/1.00  fd_pure                                 0
% 3.16/1.00  fd_pseudo                               0
% 3.16/1.00  fd_cond                                 0
% 3.16/1.00  fd_pseudo_cond                          2
% 3.16/1.00  AC symbols                              0
% 3.16/1.00  
% 3.16/1.00  ------ Schedule dynamic 5 is on 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  Current options:
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f26,conjecture,(
% 3.16/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f27,negated_conjecture,(
% 3.16/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 3.16/1.00    inference(negated_conjecture,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f52,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f27])).
% 3.16/1.00  
% 3.16/1.00  fof(f53,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.16/1.00    inference(flattening,[],[f52])).
% 3.16/1.00  
% 3.16/1.00  fof(f62,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k3_funct_2(X0,X1,sK3,X2),k2_relset_1(X0,X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f61,plain,(
% 3.16/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) => (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,sK2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(sK2,X0))) )),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,sK1,X3,X2),k2_relset_1(X0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X3,X0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(sK1))) )),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f59,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f63,plain,(
% 3.16/1.00    (((~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,sK0)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f62,f61,f60,f59])).
% 3.16/1.00  
% 3.16/1.00  fof(f107,plain,(
% 3.16/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f22,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f45,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.16/1.00    inference(ennf_transformation,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f97,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f45])).
% 3.16/1.00  
% 3.16/1.00  fof(f18,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f41,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f18])).
% 3.16/1.00  
% 3.16/1.00  fof(f91,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f41])).
% 3.16/1.00  
% 3.16/1.00  fof(f21,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f44,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f21])).
% 3.16/1.00  
% 3.16/1.00  fof(f94,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f19,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f19])).
% 3.16/1.00  
% 3.16/1.00  fof(f92,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f42])).
% 3.16/1.00  
% 3.16/1.00  fof(f20,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f43,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f20])).
% 3.16/1.00  
% 3.16/1.00  fof(f93,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f43])).
% 3.16/1.00  
% 3.16/1.00  fof(f25,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f50,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.16/1.00    inference(ennf_transformation,[],[f25])).
% 3.16/1.00  
% 3.16/1.00  fof(f51,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.16/1.00    inference(flattening,[],[f50])).
% 3.16/1.00  
% 3.16/1.00  fof(f100,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f51])).
% 3.16/1.00  
% 3.16/1.00  fof(f106,plain,(
% 3.16/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f105,plain,(
% 3.16/1.00    v1_funct_1(sK3)),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f103,plain,(
% 3.16/1.00    ~v1_xboole_0(sK1)),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f5,axiom,(
% 3.16/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f28,plain,(
% 3.16/1.00    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f5])).
% 3.16/1.00  
% 3.16/1.00  fof(f29,plain,(
% 3.16/1.00    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.16/1.00    inference(flattening,[],[f28])).
% 3.16/1.00  
% 3.16/1.00  fof(f70,plain,(
% 3.16/1.00    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f4,axiom,(
% 3.16/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f69,plain,(
% 3.16/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f4])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f54,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(nnf_transformation,[],[f2])).
% 3.16/1.00  
% 3.16/1.00  fof(f55,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(flattening,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f65,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.16/1.00    inference(cnf_transformation,[],[f55])).
% 3.16/1.00  
% 3.16/1.00  fof(f110,plain,(
% 3.16/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/1.00    inference(equality_resolution,[],[f65])).
% 3.16/1.00  
% 3.16/1.00  fof(f17,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f17])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f90,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f104,plain,(
% 3.16/1.00    m1_subset_1(sK2,sK0)),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f23,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f47,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.16/1.00    inference(flattening,[],[f46])).
% 3.16/1.00  
% 3.16/1.00  fof(f98,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f47])).
% 3.16/1.00  
% 3.16/1.00  fof(f102,plain,(
% 3.16/1.00    ~v1_xboole_0(sK0)),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f108,plain,(
% 3.16/1.00    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 3.16/1.00    inference(cnf_transformation,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,axiom,(
% 3.16/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f79,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f12,axiom,(
% 3.16/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f82,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f57,plain,(
% 3.16/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.16/1.00    inference(nnf_transformation,[],[f33])).
% 3.16/1.00  
% 3.16/1.00  fof(f75,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f57])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_39,negated_conjecture,
% 3.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3109,plain,
% 3.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_32,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3112,plain,
% 3.16/1.00      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_7497,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = k1_relset_1(sK0,sK1,sK3) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3109,c_3112]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_27,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3117,plain,
% 3.16/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4603,plain,
% 3.16/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3109,c_3117]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_31,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3113,plain,
% 3.16/1.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6650,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK1,sK3,sK0) = k2_relset_1(sK0,sK1,sK3) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3109,c_3113]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_28,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3116,plain,
% 3.16/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4324,plain,
% 3.16/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3109,c_3116]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6652,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK1,sK3,sK0) = k2_relat_1(sK3) ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_6650,c_4324]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_29,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.16/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3115,plain,
% 3.16/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5542,plain,
% 3.16/1.00      ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3109,c_3115]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6936,plain,
% 3.16/1.00      ( k9_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5542,c_6652]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_37,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_40,negated_conjecture,
% 3.16/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_537,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 3.16/1.00      | sK3 != X0
% 3.16/1.00      | sK1 != X2
% 3.16/1.00      | sK0 != X1
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_40]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_538,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/1.00      | ~ v1_funct_1(sK3)
% 3.16/1.00      | k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = sK0
% 3.16/1.00      | k1_xboole_0 = sK1 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_41,negated_conjecture,
% 3.16/1.00      ( v1_funct_1(sK3) ),
% 3.16/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_540,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK0)) = sK0
% 3.16/1.00      | k1_xboole_0 = sK1 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_538,c_41,c_39]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6067,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK0)) = sK0
% 3.16/1.00      | sK1 = k1_xboole_0 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_5542,c_540]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_43,negated_conjecture,
% 3.16/1.00      ( ~ v1_xboole_0(sK1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6,plain,
% 3.16/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_132,plain,
% 3.16/1.00      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.16/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.16/1.00      | v1_xboole_0(k1_xboole_0) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5,plain,
% 3.16/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_135,plain,
% 3.16/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3,plain,
% 3.16/1.00      ( r1_tarski(X0,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_139,plain,
% 3.16/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2256,plain,
% 3.16/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.16/1.00      theory(equality) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3426,plain,
% 3.16/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2256]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3428,plain,
% 3.16/1.00      ( v1_xboole_0(sK1)
% 3.16/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.16/1.00      | sK1 != k1_xboole_0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3426]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6259,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK0)) = sK0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_6067,c_43,c_132,c_135,c_139,c_3428]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6939,plain,
% 3.16/1.00      ( k8_relset_1(sK0,sK1,sK3,k2_relat_1(sK3)) = sK0 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_6936,c_6259]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_7499,plain,
% 3.16/1.00      ( k1_relat_1(sK3) = sK0 ),
% 3.16/1.00      inference(light_normalisation,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_7497,c_4603,c_6652,c_6939]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_26,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_613,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | sK3 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_41]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_614,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.16/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 3.16/1.00      | ~ v1_relat_1(sK3) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_613]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3102,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.16/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 3.16/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_42,negated_conjecture,
% 3.16/1.00      ( m1_subset_1(sK2,sK0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3108,plain,
% 3.16/1.00      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_34,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X3,X1)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | ~ v1_funct_1(X0)
% 3.16/1.00      | v1_xboole_0(X1)
% 3.16/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.16/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_566,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,X1)
% 3.16/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.16/1.00      | ~ v1_funct_1(X2)
% 3.16/1.00      | v1_xboole_0(X1)
% 3.16/1.00      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 3.16/1.00      | sK3 != X2
% 3.16/1.00      | sK1 != X3
% 3.16/1.00      | sK0 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_34,c_40]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_567,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,sK0)
% 3.16/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/1.00      | ~ v1_funct_1(sK3)
% 3.16/1.00      | v1_xboole_0(sK0)
% 3.16/1.00      | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_566]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_44,negated_conjecture,
% 3.16/1.00      ( ~ v1_xboole_0(sK0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_571,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,sK0)
% 3.16/1.00      | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_567,c_44,c_41,c_39]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3104,plain,
% 3.16/1.00      ( k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0)
% 3.16/1.00      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3526,plain,
% 3.16/1.00      ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3108,c_3104]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_38,negated_conjecture,
% 3.16/1.00      ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3110,plain,
% 3.16/1.00      ( r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3528,plain,
% 3.16/1.00      ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_3526,c_3110]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4326,plain,
% 3.16/1.00      ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_4324,c_3528]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4461,plain,
% 3.16/1.00      ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3102,c_4326]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_50,plain,
% 3.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_15,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3411,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | v1_relat_1(X0)
% 3.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3660,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.16/1.00      | v1_relat_1(sK3) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3411]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3661,plain,
% 3.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3660]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_18,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3762,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3763,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3762]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4464,plain,
% 3.16/1.00      ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4461,c_50,c_3661,c_3763]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_7822,plain,
% 3.16/1.00      ( r2_hidden(sK2,sK0) != iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_7499,c_4464]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_14,plain,
% 3.16/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_898,plain,
% 3.16/1.00      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | sK2 != X0 | sK0 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_42]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_899,plain,
% 3.16/1.00      ( r2_hidden(sK2,sK0) | v1_xboole_0(sK0) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_898]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_900,plain,
% 3.16/1.00      ( r2_hidden(sK2,sK0) = iProver_top
% 3.16/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_45,plain,
% 3.16/1.00      ( v1_xboole_0(sK0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(contradiction,plain,
% 3.16/1.00      ( $false ),
% 3.16/1.00      inference(minisat,[status(thm)],[c_7822,c_900,c_45]) ).
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  ------                               Statistics
% 3.16/1.00  
% 3.16/1.00  ------ General
% 3.16/1.00  
% 3.16/1.00  abstr_ref_over_cycles:                  0
% 3.16/1.00  abstr_ref_under_cycles:                 0
% 3.16/1.00  gc_basic_clause_elim:                   0
% 3.16/1.00  forced_gc_time:                         0
% 3.16/1.00  parsing_time:                           0.012
% 3.16/1.00  unif_index_cands_time:                  0.
% 3.16/1.00  unif_index_add_time:                    0.
% 3.16/1.00  orderings_time:                         0.
% 3.16/1.00  out_proof_time:                         0.01
% 3.16/1.00  total_time:                             0.317
% 3.16/1.00  num_of_symbols:                         60
% 3.16/1.00  num_of_terms:                           7151
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing
% 3.16/1.00  
% 3.16/1.00  num_of_splits:                          0
% 3.16/1.00  num_of_split_atoms:                     0
% 3.16/1.00  num_of_reused_defs:                     0
% 3.16/1.00  num_eq_ax_congr_red:                    43
% 3.16/1.00  num_of_sem_filtered_clauses:            1
% 3.16/1.00  num_of_subtypes:                        0
% 3.16/1.00  monotx_restored_types:                  0
% 3.16/1.00  sat_num_of_epr_types:                   0
% 3.16/1.00  sat_num_of_non_cyclic_types:            0
% 3.16/1.00  sat_guarded_non_collapsed_types:        0
% 3.16/1.00  num_pure_diseq_elim:                    0
% 3.16/1.00  simp_replaced_by:                       0
% 3.16/1.00  res_preprocessed:                       213
% 3.16/1.00  prep_upred:                             0
% 3.16/1.00  prep_unflattend:                        156
% 3.16/1.00  smt_new_axioms:                         0
% 3.16/1.00  pred_elim_cands:                        6
% 3.16/1.00  pred_elim:                              2
% 3.16/1.00  pred_elim_cl:                           2
% 3.16/1.00  pred_elim_cycles:                       4
% 3.16/1.00  merged_defs:                            8
% 3.16/1.00  merged_defs_ncl:                        0
% 3.16/1.00  bin_hyper_res:                          8
% 3.16/1.00  prep_cycles:                            4
% 3.16/1.00  pred_elim_time:                         0.026
% 3.16/1.00  splitting_time:                         0.
% 3.16/1.00  sem_filter_time:                        0.
% 3.16/1.00  monotx_time:                            0.
% 3.16/1.00  subtype_inf_time:                       0.
% 3.16/1.00  
% 3.16/1.00  ------ Problem properties
% 3.16/1.00  
% 3.16/1.00  clauses:                                42
% 3.16/1.00  conjectures:                            5
% 3.16/1.00  epr:                                    12
% 3.16/1.00  horn:                                   39
% 3.16/1.00  ground:                                 10
% 3.16/1.00  unary:                                  13
% 3.16/1.00  binary:                                 15
% 3.16/1.00  lits:                                   86
% 3.16/1.00  lits_eq:                                27
% 3.16/1.00  fd_pure:                                0
% 3.16/1.00  fd_pseudo:                              0
% 3.16/1.00  fd_cond:                                0
% 3.16/1.00  fd_pseudo_cond:                         2
% 3.16/1.00  ac_symbols:                             0
% 3.16/1.00  
% 3.16/1.00  ------ Propositional Solver
% 3.16/1.00  
% 3.16/1.00  prop_solver_calls:                      27
% 3.16/1.00  prop_fast_solver_calls:                 1418
% 3.16/1.00  smt_solver_calls:                       0
% 3.16/1.00  smt_fast_solver_calls:                  0
% 3.16/1.00  prop_num_of_clauses:                    2735
% 3.16/1.00  prop_preprocess_simplified:             9789
% 3.16/1.00  prop_fo_subsumed:                       30
% 3.16/1.00  prop_solver_time:                       0.
% 3.16/1.00  smt_solver_time:                        0.
% 3.16/1.00  smt_fast_solver_time:                   0.
% 3.16/1.00  prop_fast_solver_time:                  0.
% 3.16/1.00  prop_unsat_core_time:                   0.
% 3.16/1.00  
% 3.16/1.00  ------ QBF
% 3.16/1.00  
% 3.16/1.00  qbf_q_res:                              0
% 3.16/1.00  qbf_num_tautologies:                    0
% 3.16/1.00  qbf_prep_cycles:                        0
% 3.16/1.00  
% 3.16/1.00  ------ BMC1
% 3.16/1.00  
% 3.16/1.00  bmc1_current_bound:                     -1
% 3.16/1.00  bmc1_last_solved_bound:                 -1
% 3.16/1.00  bmc1_unsat_core_size:                   -1
% 3.16/1.00  bmc1_unsat_core_parents_size:           -1
% 3.16/1.00  bmc1_merge_next_fun:                    0
% 3.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation
% 3.16/1.00  
% 3.16/1.00  inst_num_of_clauses:                    854
% 3.16/1.00  inst_num_in_passive:                    164
% 3.16/1.00  inst_num_in_active:                     361
% 3.16/1.00  inst_num_in_unprocessed:                329
% 3.16/1.00  inst_num_of_loops:                      390
% 3.16/1.00  inst_num_of_learning_restarts:          0
% 3.16/1.00  inst_num_moves_active_passive:          27
% 3.16/1.00  inst_lit_activity:                      0
% 3.16/1.00  inst_lit_activity_moves:                0
% 3.16/1.00  inst_num_tautologies:                   0
% 3.16/1.00  inst_num_prop_implied:                  0
% 3.16/1.00  inst_num_existing_simplified:           0
% 3.16/1.00  inst_num_eq_res_simplified:             0
% 3.16/1.00  inst_num_child_elim:                    0
% 3.16/1.00  inst_num_of_dismatching_blockings:      93
% 3.16/1.00  inst_num_of_non_proper_insts:           774
% 3.16/1.00  inst_num_of_duplicates:                 0
% 3.16/1.00  inst_inst_num_from_inst_to_res:         0
% 3.16/1.00  inst_dismatching_checking_time:         0.
% 3.16/1.00  
% 3.16/1.00  ------ Resolution
% 3.16/1.00  
% 3.16/1.00  res_num_of_clauses:                     0
% 3.16/1.00  res_num_in_passive:                     0
% 3.16/1.00  res_num_in_active:                      0
% 3.16/1.00  res_num_of_loops:                       217
% 3.16/1.00  res_forward_subset_subsumed:            77
% 3.16/1.00  res_backward_subset_subsumed:           0
% 3.16/1.00  res_forward_subsumed:                   0
% 3.16/1.00  res_backward_subsumed:                  0
% 3.16/1.00  res_forward_subsumption_resolution:     0
% 3.16/1.00  res_backward_subsumption_resolution:    0
% 3.16/1.00  res_clause_to_clause_subsumption:       180
% 3.16/1.00  res_orphan_elimination:                 0
% 3.16/1.00  res_tautology_del:                      68
% 3.16/1.00  res_num_eq_res_simplified:              0
% 3.16/1.00  res_num_sel_changes:                    0
% 3.16/1.00  res_moves_from_active_to_pass:          0
% 3.16/1.00  
% 3.16/1.00  ------ Superposition
% 3.16/1.00  
% 3.16/1.00  sup_time_total:                         0.
% 3.16/1.00  sup_time_generating:                    0.
% 3.16/1.00  sup_time_sim_full:                      0.
% 3.16/1.00  sup_time_sim_immed:                     0.
% 3.16/1.00  
% 3.16/1.00  sup_num_of_clauses:                     89
% 3.16/1.00  sup_num_in_active:                      64
% 3.16/1.00  sup_num_in_passive:                     25
% 3.16/1.00  sup_num_of_loops:                       76
% 3.16/1.00  sup_fw_superposition:                   42
% 3.16/1.00  sup_bw_superposition:                   35
% 3.16/1.00  sup_immediate_simplified:               19
% 3.16/1.00  sup_given_eliminated:                   0
% 3.16/1.00  comparisons_done:                       0
% 3.16/1.00  comparisons_avoided:                    0
% 3.16/1.00  
% 3.16/1.00  ------ Simplifications
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  sim_fw_subset_subsumed:                 10
% 3.16/1.00  sim_bw_subset_subsumed:                 1
% 3.16/1.00  sim_fw_subsumed:                        2
% 3.16/1.00  sim_bw_subsumed:                        0
% 3.16/1.00  sim_fw_subsumption_res:                 0
% 3.16/1.00  sim_bw_subsumption_res:                 0
% 3.16/1.00  sim_tautology_del:                      8
% 3.16/1.00  sim_eq_tautology_del:                   2
% 3.16/1.00  sim_eq_res_simp:                        0
% 3.16/1.00  sim_fw_demodulated:                     0
% 3.16/1.00  sim_bw_demodulated:                     11
% 3.16/1.00  sim_light_normalised:                   8
% 3.16/1.00  sim_joinable_taut:                      0
% 3.16/1.00  sim_joinable_simp:                      0
% 3.16/1.00  sim_ac_normalised:                      0
% 3.16/1.00  sim_smt_subsumption:                    0
% 3.16/1.00  
%------------------------------------------------------------------------------
