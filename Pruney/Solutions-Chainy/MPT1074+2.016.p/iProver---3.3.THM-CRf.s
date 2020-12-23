%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:15 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  194 (28902 expanded)
%              Number of clauses        :  136 (8685 expanded)
%              Number of leaves         :   17 (8424 expanded)
%              Depth                    :   35
%              Number of atoms          :  614 (187399 expanded)
%              Number of equality atoms :  247 (14783 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK4),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK3,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
            & v1_funct_2(X3,X1,sK3)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK2,X2,X3),sK1)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1)
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_2(X3,sK2,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32,f31,f30])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_relat_1(X2),X1)
        & k1_relat_1(X2) = X0 )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_relat_1(X2),X1)
        & k1_relat_1(X2) = X0 )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = X0
      | ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_677,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_678,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_3522,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_679,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3693,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3694,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3693])).

cnf(c_4456,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3522,c_29,c_679,c_3694])).

cnf(c_4457,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4456])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3537,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4464,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4457,c_3537])).

cnf(c_3532,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_722,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_723,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | r2_hidden(sK4,k1_funct_2(X0,X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_3519,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK4,X1,X0) != iProver_top
    | r2_hidden(sK4,k1_funct_2(X1,X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_4186,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_3519])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_314,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_964,plain,
    ( r2_hidden(sK4,k1_funct_2(X0,X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_723])).

cnf(c_965,plain,
    ( r2_hidden(sK4,k1_funct_2(sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_966,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_3143,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3721,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3143])).

cnf(c_3805,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_3142,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3806,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3142])).

cnf(c_4263,plain,
    ( r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4186,c_29,c_314,c_966,c_3805,c_3806])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_707,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_708,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(X0,X1))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_3520,plain,
    ( k1_relat_1(sK4) = X0
    | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_709,plain,
    ( k1_relat_1(sK4) = X0
    | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_4029,plain,
    ( r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
    | k1_relat_1(sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3520,c_29,c_709,c_3694])).

cnf(c_4030,plain,
    ( k1_relat_1(sK4) = X0
    | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4029])).

cnf(c_4270,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_4263,c_4030])).

cnf(c_4715,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4464,c_4270])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_343,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_344,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_611,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_22])).

cnf(c_612,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_3526,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_4373,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_3526])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | k3_funct_2(sK2,X1,sK4,X0) = k1_funct_1(sK4,X0)
    | sK4 != sK4
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_612])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_20])).

cnf(c_935,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_4376,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4373,c_935])).

cnf(c_4721,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_4376])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3534,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4952,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4721,c_3534])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3533,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5499,plain,
    ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4952,c_3533])).

cnf(c_12,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_692,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_693,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_3521,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_694,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_4106,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3521,c_29,c_694,c_3694])).

cnf(c_4107,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4106])).

cnf(c_4552,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4270,c_4107])).

cnf(c_5620,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5499,c_4552])).

cnf(c_4955,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k1_xboole_0 = X0
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4721,c_3519])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_647,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_648,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_3524,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_649,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_4443,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3524,c_29,c_649,c_3694])).

cnf(c_4444,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4443])).

cnf(c_4451,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4444,c_3537])).

cnf(c_4704,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4451,c_4270])).

cnf(c_4710,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | v1_funct_2(sK4,sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4704,c_4376])).

cnf(c_5274,plain,
    ( k1_xboole_0 = X0
    | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4955,c_4710])).

cnf(c_5275,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k1_xboole_0 = X0
    | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5274])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ r2_hidden(X0,k1_funct_2(X2,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_405,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,sK1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_581,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,sK1))
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_405,c_22])).

cnf(c_582,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(X0,sK1))
    | ~ v1_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_3139,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(X0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_582])).

cnf(c_3529,plain,
    ( r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3139])).

cnf(c_583,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_3703,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3731,plain,
    ( r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3529,c_20,c_29,c_583,c_3694,c_3703])).

cnf(c_5284,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5275,c_3731])).

cnf(c_5312,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5284,c_3533])).

cnf(c_5549,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5312,c_4552])).

cnf(c_5716,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5549,c_4715])).

cnf(c_5721,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | r2_hidden(sK4,k1_funct_2(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_3519])).

cnf(c_585,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r2_hidden(sK4,k1_funct_2(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_662,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_663,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_3523,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_664,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_4097,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3523,c_29,c_664,c_3694])).

cnf(c_4098,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4097])).

cnf(c_4553,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4270,c_4098])).

cnf(c_5550,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5312,c_4553])).

cnf(c_5640,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5550,c_4704])).

cnf(c_5745,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5721,c_20,c_29,c_585,c_3694,c_3703,c_5640])).

cnf(c_6182,plain,
    ( k2_relset_1(sK2,k1_xboole_0,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5620,c_5745])).

cnf(c_6186,plain,
    ( k2_relset_1(sK2,k1_xboole_0,sK4) = k2_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6182,c_3534,c_4715])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3535,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6187,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6186,c_3535])).

cnf(c_3831,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3532,c_3534])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_185,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_185,c_18])).

cnf(c_398,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_3530,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3983,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3831,c_3530])).

cnf(c_5750,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5745,c_3983])).

cnf(c_6493,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6187,c_5750])).

cnf(c_6498,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,k1_xboole_0,sK4)) = k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4)) ),
    inference(superposition,[status(thm)],[c_4721,c_6493])).

cnf(c_5753,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),k1_xboole_0) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5745,c_3533])).

cnf(c_6697,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4)),k1_xboole_0) = iProver_top
    | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6498,c_5753])).

cnf(c_6773,plain,
    ( v1_funct_2(sK4,sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6697,c_4553])).

cnf(c_6772,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6697,c_4552])).

cnf(c_6785,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6773,c_5750,c_6187,c_6772])).

cnf(c_6790,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_6785])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6790,c_6187,c_5750])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.03/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.00  
% 3.03/1.00  ------  iProver source info
% 3.03/1.00  
% 3.03/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.00  git: non_committed_changes: false
% 3.03/1.00  git: last_make_outside_of_git: false
% 3.03/1.00  
% 3.03/1.00  ------ 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options
% 3.03/1.00  
% 3.03/1.00  --out_options                           all
% 3.03/1.00  --tptp_safe_out                         true
% 3.03/1.00  --problem_path                          ""
% 3.03/1.00  --include_path                          ""
% 3.03/1.00  --clausifier                            res/vclausify_rel
% 3.03/1.00  --clausifier_options                    --mode clausify
% 3.03/1.00  --stdin                                 false
% 3.03/1.00  --stats_out                             all
% 3.03/1.00  
% 3.03/1.00  ------ General Options
% 3.03/1.00  
% 3.03/1.00  --fof                                   false
% 3.03/1.00  --time_out_real                         305.
% 3.03/1.00  --time_out_virtual                      -1.
% 3.03/1.00  --symbol_type_check                     false
% 3.03/1.00  --clausify_out                          false
% 3.03/1.00  --sig_cnt_out                           false
% 3.03/1.00  --trig_cnt_out                          false
% 3.03/1.00  --trig_cnt_out_tolerance                1.
% 3.03/1.00  --trig_cnt_out_sk_spl                   false
% 3.03/1.00  --abstr_cl_out                          false
% 3.03/1.00  
% 3.03/1.00  ------ Global Options
% 3.03/1.00  
% 3.03/1.00  --schedule                              default
% 3.03/1.00  --add_important_lit                     false
% 3.03/1.00  --prop_solver_per_cl                    1000
% 3.03/1.00  --min_unsat_core                        false
% 3.03/1.00  --soft_assumptions                      false
% 3.03/1.00  --soft_lemma_size                       3
% 3.03/1.00  --prop_impl_unit_size                   0
% 3.03/1.00  --prop_impl_unit                        []
% 3.03/1.00  --share_sel_clauses                     true
% 3.03/1.00  --reset_solvers                         false
% 3.03/1.00  --bc_imp_inh                            [conj_cone]
% 3.03/1.00  --conj_cone_tolerance                   3.
% 3.03/1.00  --extra_neg_conj                        none
% 3.03/1.00  --large_theory_mode                     true
% 3.03/1.00  --prolific_symb_bound                   200
% 3.03/1.00  --lt_threshold                          2000
% 3.03/1.00  --clause_weak_htbl                      true
% 3.03/1.00  --gc_record_bc_elim                     false
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing Options
% 3.03/1.00  
% 3.03/1.00  --preprocessing_flag                    true
% 3.03/1.00  --time_out_prep_mult                    0.1
% 3.03/1.00  --splitting_mode                        input
% 3.03/1.00  --splitting_grd                         true
% 3.03/1.00  --splitting_cvd                         false
% 3.03/1.00  --splitting_cvd_svl                     false
% 3.03/1.00  --splitting_nvd                         32
% 3.03/1.00  --sub_typing                            true
% 3.03/1.00  --prep_gs_sim                           true
% 3.03/1.00  --prep_unflatten                        true
% 3.03/1.00  --prep_res_sim                          true
% 3.03/1.00  --prep_upred                            true
% 3.03/1.00  --prep_sem_filter                       exhaustive
% 3.03/1.00  --prep_sem_filter_out                   false
% 3.03/1.00  --pred_elim                             true
% 3.03/1.00  --res_sim_input                         true
% 3.03/1.00  --eq_ax_congr_red                       true
% 3.03/1.00  --pure_diseq_elim                       true
% 3.03/1.00  --brand_transform                       false
% 3.03/1.00  --non_eq_to_eq                          false
% 3.03/1.00  --prep_def_merge                        true
% 3.03/1.00  --prep_def_merge_prop_impl              false
% 3.03/1.00  --prep_def_merge_mbd                    true
% 3.03/1.00  --prep_def_merge_tr_red                 false
% 3.03/1.00  --prep_def_merge_tr_cl                  false
% 3.03/1.00  --smt_preprocessing                     true
% 3.03/1.00  --smt_ac_axioms                         fast
% 3.03/1.00  --preprocessed_out                      false
% 3.03/1.00  --preprocessed_stats                    false
% 3.03/1.00  
% 3.03/1.00  ------ Abstraction refinement Options
% 3.03/1.00  
% 3.03/1.00  --abstr_ref                             []
% 3.03/1.00  --abstr_ref_prep                        false
% 3.03/1.00  --abstr_ref_until_sat                   false
% 3.03/1.00  --abstr_ref_sig_restrict                funpre
% 3.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.00  --abstr_ref_under                       []
% 3.03/1.00  
% 3.03/1.00  ------ SAT Options
% 3.03/1.00  
% 3.03/1.00  --sat_mode                              false
% 3.03/1.00  --sat_fm_restart_options                ""
% 3.03/1.00  --sat_gr_def                            false
% 3.03/1.00  --sat_epr_types                         true
% 3.03/1.00  --sat_non_cyclic_types                  false
% 3.03/1.00  --sat_finite_models                     false
% 3.03/1.00  --sat_fm_lemmas                         false
% 3.03/1.00  --sat_fm_prep                           false
% 3.03/1.00  --sat_fm_uc_incr                        true
% 3.03/1.00  --sat_out_model                         small
% 3.03/1.00  --sat_out_clauses                       false
% 3.03/1.00  
% 3.03/1.00  ------ QBF Options
% 3.03/1.00  
% 3.03/1.00  --qbf_mode                              false
% 3.03/1.00  --qbf_elim_univ                         false
% 3.03/1.00  --qbf_dom_inst                          none
% 3.03/1.00  --qbf_dom_pre_inst                      false
% 3.03/1.00  --qbf_sk_in                             false
% 3.03/1.00  --qbf_pred_elim                         true
% 3.03/1.00  --qbf_split                             512
% 3.03/1.00  
% 3.03/1.00  ------ BMC1 Options
% 3.03/1.00  
% 3.03/1.00  --bmc1_incremental                      false
% 3.03/1.00  --bmc1_axioms                           reachable_all
% 3.03/1.00  --bmc1_min_bound                        0
% 3.03/1.00  --bmc1_max_bound                        -1
% 3.03/1.00  --bmc1_max_bound_default                -1
% 3.03/1.00  --bmc1_symbol_reachability              true
% 3.03/1.00  --bmc1_property_lemmas                  false
% 3.03/1.00  --bmc1_k_induction                      false
% 3.03/1.00  --bmc1_non_equiv_states                 false
% 3.03/1.00  --bmc1_deadlock                         false
% 3.03/1.00  --bmc1_ucm                              false
% 3.03/1.00  --bmc1_add_unsat_core                   none
% 3.03/1.00  --bmc1_unsat_core_children              false
% 3.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.00  --bmc1_out_stat                         full
% 3.03/1.00  --bmc1_ground_init                      false
% 3.03/1.00  --bmc1_pre_inst_next_state              false
% 3.03/1.00  --bmc1_pre_inst_state                   false
% 3.03/1.00  --bmc1_pre_inst_reach_state             false
% 3.03/1.00  --bmc1_out_unsat_core                   false
% 3.03/1.00  --bmc1_aig_witness_out                  false
% 3.03/1.00  --bmc1_verbose                          false
% 3.03/1.00  --bmc1_dump_clauses_tptp                false
% 3.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.00  --bmc1_dump_file                        -
% 3.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.00  --bmc1_ucm_extend_mode                  1
% 3.03/1.00  --bmc1_ucm_init_mode                    2
% 3.03/1.00  --bmc1_ucm_cone_mode                    none
% 3.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.00  --bmc1_ucm_relax_model                  4
% 3.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.00  --bmc1_ucm_layered_model                none
% 3.03/1.00  --bmc1_ucm_max_lemma_size               10
% 3.03/1.00  
% 3.03/1.00  ------ AIG Options
% 3.03/1.00  
% 3.03/1.00  --aig_mode                              false
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation Options
% 3.03/1.00  
% 3.03/1.00  --instantiation_flag                    true
% 3.03/1.00  --inst_sos_flag                         false
% 3.03/1.00  --inst_sos_phase                        true
% 3.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel_side                     num_symb
% 3.03/1.00  --inst_solver_per_active                1400
% 3.03/1.00  --inst_solver_calls_frac                1.
% 3.03/1.00  --inst_passive_queue_type               priority_queues
% 3.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.00  --inst_passive_queues_freq              [25;2]
% 3.03/1.00  --inst_dismatching                      true
% 3.03/1.00  --inst_eager_unprocessed_to_passive     true
% 3.03/1.00  --inst_prop_sim_given                   true
% 3.03/1.00  --inst_prop_sim_new                     false
% 3.03/1.00  --inst_subs_new                         false
% 3.03/1.00  --inst_eq_res_simp                      false
% 3.03/1.00  --inst_subs_given                       false
% 3.03/1.00  --inst_orphan_elimination               true
% 3.03/1.00  --inst_learning_loop_flag               true
% 3.03/1.00  --inst_learning_start                   3000
% 3.03/1.00  --inst_learning_factor                  2
% 3.03/1.00  --inst_start_prop_sim_after_learn       3
% 3.03/1.00  --inst_sel_renew                        solver
% 3.03/1.00  --inst_lit_activity_flag                true
% 3.03/1.00  --inst_restr_to_given                   false
% 3.03/1.00  --inst_activity_threshold               500
% 3.03/1.00  --inst_out_proof                        true
% 3.03/1.00  
% 3.03/1.00  ------ Resolution Options
% 3.03/1.00  
% 3.03/1.00  --resolution_flag                       true
% 3.03/1.00  --res_lit_sel                           adaptive
% 3.03/1.00  --res_lit_sel_side                      none
% 3.03/1.00  --res_ordering                          kbo
% 3.03/1.00  --res_to_prop_solver                    active
% 3.03/1.00  --res_prop_simpl_new                    false
% 3.03/1.00  --res_prop_simpl_given                  true
% 3.03/1.00  --res_passive_queue_type                priority_queues
% 3.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.00  --res_passive_queues_freq               [15;5]
% 3.03/1.00  --res_forward_subs                      full
% 3.03/1.00  --res_backward_subs                     full
% 3.03/1.00  --res_forward_subs_resolution           true
% 3.03/1.00  --res_backward_subs_resolution          true
% 3.03/1.00  --res_orphan_elimination                true
% 3.03/1.00  --res_time_limit                        2.
% 3.03/1.00  --res_out_proof                         true
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Options
% 3.03/1.00  
% 3.03/1.00  --superposition_flag                    true
% 3.03/1.00  --sup_passive_queue_type                priority_queues
% 3.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.00  --demod_completeness_check              fast
% 3.03/1.00  --demod_use_ground                      true
% 3.03/1.00  --sup_to_prop_solver                    passive
% 3.03/1.00  --sup_prop_simpl_new                    true
% 3.03/1.00  --sup_prop_simpl_given                  true
% 3.03/1.00  --sup_fun_splitting                     false
% 3.03/1.00  --sup_smt_interval                      50000
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Simplification Setup
% 3.03/1.00  
% 3.03/1.00  --sup_indices_passive                   []
% 3.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_full_bw                           [BwDemod]
% 3.03/1.00  --sup_immed_triv                        [TrivRules]
% 3.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_immed_bw_main                     []
% 3.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  
% 3.03/1.00  ------ Combination Options
% 3.03/1.00  
% 3.03/1.00  --comb_res_mult                         3
% 3.03/1.00  --comb_sup_mult                         2
% 3.03/1.00  --comb_inst_mult                        10
% 3.03/1.00  
% 3.03/1.00  ------ Debug Options
% 3.03/1.00  
% 3.03/1.00  --dbg_backtrace                         false
% 3.03/1.00  --dbg_dump_prop_clauses                 false
% 3.03/1.00  --dbg_dump_prop_clauses_file            -
% 3.03/1.00  --dbg_out_stat                          false
% 3.03/1.00  ------ Parsing...
% 3.03/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.00  ------ Proving...
% 3.03/1.00  ------ Problem Properties 
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  clauses                                 22
% 3.03/1.00  conjectures                             3
% 3.03/1.00  EPR                                     4
% 3.03/1.00  Horn                                    19
% 3.03/1.00  unary                                   5
% 3.03/1.00  binary                                  6
% 3.03/1.00  lits                                    53
% 3.03/1.00  lits eq                                 8
% 3.03/1.00  fd_pure                                 0
% 3.03/1.00  fd_pseudo                               0
% 3.03/1.00  fd_cond                                 2
% 3.03/1.00  fd_pseudo_cond                          0
% 3.03/1.00  AC symbols                              0
% 3.03/1.00  
% 3.03/1.00  ------ Schedule dynamic 5 is on 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  ------ 
% 3.03/1.00  Current options:
% 3.03/1.00  ------ 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options
% 3.03/1.00  
% 3.03/1.00  --out_options                           all
% 3.03/1.00  --tptp_safe_out                         true
% 3.03/1.00  --problem_path                          ""
% 3.03/1.00  --include_path                          ""
% 3.03/1.00  --clausifier                            res/vclausify_rel
% 3.03/1.00  --clausifier_options                    --mode clausify
% 3.03/1.00  --stdin                                 false
% 3.03/1.00  --stats_out                             all
% 3.03/1.00  
% 3.03/1.00  ------ General Options
% 3.03/1.00  
% 3.03/1.00  --fof                                   false
% 3.03/1.00  --time_out_real                         305.
% 3.03/1.00  --time_out_virtual                      -1.
% 3.03/1.00  --symbol_type_check                     false
% 3.03/1.00  --clausify_out                          false
% 3.03/1.00  --sig_cnt_out                           false
% 3.03/1.00  --trig_cnt_out                          false
% 3.03/1.00  --trig_cnt_out_tolerance                1.
% 3.03/1.00  --trig_cnt_out_sk_spl                   false
% 3.03/1.00  --abstr_cl_out                          false
% 3.03/1.00  
% 3.03/1.00  ------ Global Options
% 3.03/1.00  
% 3.03/1.00  --schedule                              default
% 3.03/1.00  --add_important_lit                     false
% 3.03/1.00  --prop_solver_per_cl                    1000
% 3.03/1.00  --min_unsat_core                        false
% 3.03/1.00  --soft_assumptions                      false
% 3.03/1.00  --soft_lemma_size                       3
% 3.03/1.00  --prop_impl_unit_size                   0
% 3.03/1.00  --prop_impl_unit                        []
% 3.03/1.00  --share_sel_clauses                     true
% 3.03/1.00  --reset_solvers                         false
% 3.03/1.00  --bc_imp_inh                            [conj_cone]
% 3.03/1.00  --conj_cone_tolerance                   3.
% 3.03/1.00  --extra_neg_conj                        none
% 3.03/1.00  --large_theory_mode                     true
% 3.03/1.00  --prolific_symb_bound                   200
% 3.03/1.00  --lt_threshold                          2000
% 3.03/1.00  --clause_weak_htbl                      true
% 3.03/1.00  --gc_record_bc_elim                     false
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing Options
% 3.03/1.00  
% 3.03/1.00  --preprocessing_flag                    true
% 3.03/1.00  --time_out_prep_mult                    0.1
% 3.03/1.00  --splitting_mode                        input
% 3.03/1.00  --splitting_grd                         true
% 3.03/1.00  --splitting_cvd                         false
% 3.03/1.00  --splitting_cvd_svl                     false
% 3.03/1.00  --splitting_nvd                         32
% 3.03/1.00  --sub_typing                            true
% 3.03/1.00  --prep_gs_sim                           true
% 3.03/1.00  --prep_unflatten                        true
% 3.03/1.00  --prep_res_sim                          true
% 3.03/1.00  --prep_upred                            true
% 3.03/1.00  --prep_sem_filter                       exhaustive
% 3.03/1.00  --prep_sem_filter_out                   false
% 3.03/1.00  --pred_elim                             true
% 3.03/1.00  --res_sim_input                         true
% 3.03/1.00  --eq_ax_congr_red                       true
% 3.03/1.00  --pure_diseq_elim                       true
% 3.03/1.00  --brand_transform                       false
% 3.03/1.00  --non_eq_to_eq                          false
% 3.03/1.00  --prep_def_merge                        true
% 3.03/1.00  --prep_def_merge_prop_impl              false
% 3.03/1.00  --prep_def_merge_mbd                    true
% 3.03/1.00  --prep_def_merge_tr_red                 false
% 3.03/1.00  --prep_def_merge_tr_cl                  false
% 3.03/1.00  --smt_preprocessing                     true
% 3.03/1.00  --smt_ac_axioms                         fast
% 3.03/1.00  --preprocessed_out                      false
% 3.03/1.00  --preprocessed_stats                    false
% 3.03/1.00  
% 3.03/1.00  ------ Abstraction refinement Options
% 3.03/1.00  
% 3.03/1.00  --abstr_ref                             []
% 3.03/1.00  --abstr_ref_prep                        false
% 3.03/1.00  --abstr_ref_until_sat                   false
% 3.03/1.00  --abstr_ref_sig_restrict                funpre
% 3.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.00  --abstr_ref_under                       []
% 3.03/1.00  
% 3.03/1.00  ------ SAT Options
% 3.03/1.00  
% 3.03/1.00  --sat_mode                              false
% 3.03/1.00  --sat_fm_restart_options                ""
% 3.03/1.00  --sat_gr_def                            false
% 3.03/1.00  --sat_epr_types                         true
% 3.03/1.00  --sat_non_cyclic_types                  false
% 3.03/1.00  --sat_finite_models                     false
% 3.03/1.00  --sat_fm_lemmas                         false
% 3.03/1.00  --sat_fm_prep                           false
% 3.03/1.00  --sat_fm_uc_incr                        true
% 3.03/1.00  --sat_out_model                         small
% 3.03/1.00  --sat_out_clauses                       false
% 3.03/1.00  
% 3.03/1.00  ------ QBF Options
% 3.03/1.00  
% 3.03/1.00  --qbf_mode                              false
% 3.03/1.00  --qbf_elim_univ                         false
% 3.03/1.00  --qbf_dom_inst                          none
% 3.03/1.00  --qbf_dom_pre_inst                      false
% 3.03/1.00  --qbf_sk_in                             false
% 3.03/1.00  --qbf_pred_elim                         true
% 3.03/1.00  --qbf_split                             512
% 3.03/1.00  
% 3.03/1.00  ------ BMC1 Options
% 3.03/1.00  
% 3.03/1.00  --bmc1_incremental                      false
% 3.03/1.00  --bmc1_axioms                           reachable_all
% 3.03/1.00  --bmc1_min_bound                        0
% 3.03/1.00  --bmc1_max_bound                        -1
% 3.03/1.00  --bmc1_max_bound_default                -1
% 3.03/1.00  --bmc1_symbol_reachability              true
% 3.03/1.00  --bmc1_property_lemmas                  false
% 3.03/1.00  --bmc1_k_induction                      false
% 3.03/1.00  --bmc1_non_equiv_states                 false
% 3.03/1.00  --bmc1_deadlock                         false
% 3.03/1.00  --bmc1_ucm                              false
% 3.03/1.00  --bmc1_add_unsat_core                   none
% 3.03/1.00  --bmc1_unsat_core_children              false
% 3.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.00  --bmc1_out_stat                         full
% 3.03/1.00  --bmc1_ground_init                      false
% 3.03/1.00  --bmc1_pre_inst_next_state              false
% 3.03/1.00  --bmc1_pre_inst_state                   false
% 3.03/1.00  --bmc1_pre_inst_reach_state             false
% 3.03/1.00  --bmc1_out_unsat_core                   false
% 3.03/1.00  --bmc1_aig_witness_out                  false
% 3.03/1.00  --bmc1_verbose                          false
% 3.03/1.00  --bmc1_dump_clauses_tptp                false
% 3.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.00  --bmc1_dump_file                        -
% 3.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.00  --bmc1_ucm_extend_mode                  1
% 3.03/1.00  --bmc1_ucm_init_mode                    2
% 3.03/1.00  --bmc1_ucm_cone_mode                    none
% 3.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.00  --bmc1_ucm_relax_model                  4
% 3.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.00  --bmc1_ucm_layered_model                none
% 3.03/1.00  --bmc1_ucm_max_lemma_size               10
% 3.03/1.00  
% 3.03/1.00  ------ AIG Options
% 3.03/1.00  
% 3.03/1.00  --aig_mode                              false
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation Options
% 3.03/1.00  
% 3.03/1.00  --instantiation_flag                    true
% 3.03/1.00  --inst_sos_flag                         false
% 3.03/1.00  --inst_sos_phase                        true
% 3.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel_side                     none
% 3.03/1.00  --inst_solver_per_active                1400
% 3.03/1.00  --inst_solver_calls_frac                1.
% 3.03/1.00  --inst_passive_queue_type               priority_queues
% 3.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.00  --inst_passive_queues_freq              [25;2]
% 3.03/1.00  --inst_dismatching                      true
% 3.03/1.00  --inst_eager_unprocessed_to_passive     true
% 3.03/1.00  --inst_prop_sim_given                   true
% 3.03/1.00  --inst_prop_sim_new                     false
% 3.03/1.00  --inst_subs_new                         false
% 3.03/1.00  --inst_eq_res_simp                      false
% 3.03/1.00  --inst_subs_given                       false
% 3.03/1.00  --inst_orphan_elimination               true
% 3.03/1.00  --inst_learning_loop_flag               true
% 3.03/1.00  --inst_learning_start                   3000
% 3.03/1.00  --inst_learning_factor                  2
% 3.03/1.00  --inst_start_prop_sim_after_learn       3
% 3.03/1.00  --inst_sel_renew                        solver
% 3.03/1.00  --inst_lit_activity_flag                true
% 3.03/1.00  --inst_restr_to_given                   false
% 3.03/1.00  --inst_activity_threshold               500
% 3.03/1.00  --inst_out_proof                        true
% 3.03/1.00  
% 3.03/1.00  ------ Resolution Options
% 3.03/1.00  
% 3.03/1.00  --resolution_flag                       false
% 3.03/1.00  --res_lit_sel                           adaptive
% 3.03/1.00  --res_lit_sel_side                      none
% 3.03/1.00  --res_ordering                          kbo
% 3.03/1.00  --res_to_prop_solver                    active
% 3.03/1.00  --res_prop_simpl_new                    false
% 3.03/1.00  --res_prop_simpl_given                  true
% 3.03/1.00  --res_passive_queue_type                priority_queues
% 3.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.00  --res_passive_queues_freq               [15;5]
% 3.03/1.00  --res_forward_subs                      full
% 3.03/1.00  --res_backward_subs                     full
% 3.03/1.00  --res_forward_subs_resolution           true
% 3.03/1.00  --res_backward_subs_resolution          true
% 3.03/1.00  --res_orphan_elimination                true
% 3.03/1.00  --res_time_limit                        2.
% 3.03/1.00  --res_out_proof                         true
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Options
% 3.03/1.00  
% 3.03/1.00  --superposition_flag                    true
% 3.03/1.00  --sup_passive_queue_type                priority_queues
% 3.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.00  --demod_completeness_check              fast
% 3.03/1.00  --demod_use_ground                      true
% 3.03/1.00  --sup_to_prop_solver                    passive
% 3.03/1.00  --sup_prop_simpl_new                    true
% 3.03/1.00  --sup_prop_simpl_given                  true
% 3.03/1.00  --sup_fun_splitting                     false
% 3.03/1.00  --sup_smt_interval                      50000
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Simplification Setup
% 3.03/1.00  
% 3.03/1.00  --sup_indices_passive                   []
% 3.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_full_bw                           [BwDemod]
% 3.03/1.00  --sup_immed_triv                        [TrivRules]
% 3.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_immed_bw_main                     []
% 3.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  
% 3.03/1.00  ------ Combination Options
% 3.03/1.00  
% 3.03/1.00  --comb_res_mult                         3
% 3.03/1.00  --comb_sup_mult                         2
% 3.03/1.00  --comb_inst_mult                        10
% 3.03/1.00  
% 3.03/1.00  ------ Debug Options
% 3.03/1.00  
% 3.03/1.00  --dbg_backtrace                         false
% 3.03/1.00  --dbg_dump_prop_clauses                 false
% 3.03/1.00  --dbg_dump_prop_clauses_file            -
% 3.03/1.00  --dbg_out_stat                          false
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  ------ Proving...
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  % SZS status Theorem for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  fof(f10,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f23,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f10])).
% 3.03/1.00  
% 3.03/1.00  fof(f24,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.00    inference(flattening,[],[f23])).
% 3.03/1.00  
% 3.03/1.00  fof(f28,plain,(
% 3.03/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f29,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 3.03/1.00  
% 3.03/1.00  fof(f50,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f61,plain,(
% 3.03/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(equality_resolution,[],[f50])).
% 3.03/1.00  
% 3.03/1.00  fof(f11,conjecture,(
% 3.03/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f12,negated_conjecture,(
% 3.03/1.00    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.03/1.00    inference(negated_conjecture,[],[f11])).
% 3.03/1.00  
% 3.03/1.00  fof(f25,plain,(
% 3.03/1.00    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.03/1.00    inference(ennf_transformation,[],[f12])).
% 3.03/1.00  
% 3.03/1.00  fof(f26,plain,(
% 3.03/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.03/1.00    inference(flattening,[],[f25])).
% 3.03/1.00  
% 3.03/1.00  fof(f32,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f31,plain,(
% 3.03/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f30,plain,(
% 3.03/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f33,plain,(
% 3.03/1.00    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32,f31,f30])).
% 3.03/1.00  
% 3.03/1.00  fof(f54,plain,(
% 3.03/1.00    v1_funct_1(sK4)),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f56,plain,(
% 3.03/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f4,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f14,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f4])).
% 3.03/1.00  
% 3.03/1.00  fof(f38,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f14])).
% 3.03/1.00  
% 3.03/1.00  fof(f2,axiom,(
% 3.03/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f13,plain,(
% 3.03/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.03/1.00    inference(ennf_transformation,[],[f2])).
% 3.03/1.00  
% 3.03/1.00  fof(f35,plain,(
% 3.03/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f13])).
% 3.03/1.00  
% 3.03/1.00  fof(f8,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f19,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f8])).
% 3.03/1.00  
% 3.03/1.00  fof(f20,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.03/1.00    inference(flattening,[],[f19])).
% 3.03/1.00  
% 3.03/1.00  fof(f42,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f20])).
% 3.03/1.00  
% 3.03/1.00  fof(f1,axiom,(
% 3.03/1.00    v1_xboole_0(k1_xboole_0)),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f34,plain,(
% 3.03/1.00    v1_xboole_0(k1_xboole_0)),
% 3.03/1.00    inference(cnf_transformation,[],[f1])).
% 3.03/1.00  
% 3.03/1.00  fof(f53,plain,(
% 3.03/1.00    ~v1_xboole_0(sK3)),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f55,plain,(
% 3.03/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f9,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f21,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (((r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0) | ~r2_hidden(X2,k1_funct_2(X0,X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f9])).
% 3.03/1.00  
% 3.03/1.00  fof(f22,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0) | ~r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.00    inference(flattening,[],[f21])).
% 3.03/1.00  
% 3.03/1.00  fof(f44,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = X0 | ~r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f22])).
% 3.03/1.00  
% 3.03/1.00  fof(f7,axiom,(
% 3.03/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f17,plain,(
% 3.03/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f7])).
% 3.03/1.00  
% 3.03/1.00  fof(f18,plain,(
% 3.03/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.03/1.00    inference(flattening,[],[f17])).
% 3.03/1.00  
% 3.03/1.00  fof(f41,plain,(
% 3.03/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f18])).
% 3.03/1.00  
% 3.03/1.00  fof(f52,plain,(
% 3.03/1.00    ~v1_xboole_0(sK2)),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f6,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f16,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f6])).
% 3.03/1.00  
% 3.03/1.00  fof(f40,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f16])).
% 3.03/1.00  
% 3.03/1.00  fof(f57,plain,(
% 3.03/1.00    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f51,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f60,plain,(
% 3.03/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(equality_resolution,[],[f51])).
% 3.03/1.00  
% 3.03/1.00  fof(f48,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f63,plain,(
% 3.03/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(equality_resolution,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f45,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),X1) | ~r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f22])).
% 3.03/1.00  
% 3.03/1.00  fof(f58,plain,(
% 3.03/1.00    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f49,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f62,plain,(
% 3.03/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.00    inference(equality_resolution,[],[f49])).
% 3.03/1.00  
% 3.03/1.00  fof(f5,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f15,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f5])).
% 3.03/1.00  
% 3.03/1.00  fof(f39,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f15])).
% 3.03/1.00  
% 3.03/1.00  fof(f3,axiom,(
% 3.03/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f27,plain,(
% 3.03/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.03/1.00    inference(nnf_transformation,[],[f3])).
% 3.03/1.00  
% 3.03/1.00  fof(f36,plain,(
% 3.03/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f27])).
% 3.03/1.00  
% 3.03/1.00  cnf(c_13,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_22,negated_conjecture,
% 3.03/1.00      ( v1_funct_1(sK4) ),
% 3.03/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_677,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_678,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.03/1.00      | ~ v1_relat_1(sK4) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_677]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3522,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_20,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.03/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_29,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_679,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3693,plain,
% 3.03/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.03/1.00      | v1_relat_1(sK4) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3694,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3693]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4456,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3522,c_29,c_679,c_3694]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4457,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_4456]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3537,plain,
% 3.03/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.03/1.00      | m1_subset_1(X0,X1) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4464,plain,
% 3.03/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4457,c_3537]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3532,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_9,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | k1_xboole_0 = X2 ),
% 3.03/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_722,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | sK4 != X0
% 3.03/1.00      | k1_xboole_0 = X2 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_723,plain,
% 3.03/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X0,X1))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/1.00      | k1_xboole_0 = X1 ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_722]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3519,plain,
% 3.03/1.00      ( k1_xboole_0 = X0
% 3.03/1.00      | v1_funct_2(sK4,X1,X0) != iProver_top
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X1,X0)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4186,plain,
% 3.03/1.00      ( sK3 = k1_xboole_0
% 3.03/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3532,c_3519]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_0,plain,
% 3.03/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_23,negated_conjecture,
% 3.03/1.00      ( ~ v1_xboole_0(sK3) ),
% 3.03/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_314,plain,
% 3.03/1.00      ( sK3 != k1_xboole_0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_21,negated_conjecture,
% 3.03/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.03/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_964,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(X0,X1))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/1.00      | sK4 != sK4
% 3.03/1.00      | sK3 != X1
% 3.03/1.00      | sK2 != X0
% 3.03/1.00      | k1_xboole_0 = X1 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_723]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_965,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(sK2,sK3))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.03/1.00      | k1_xboole_0 = sK3 ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_964]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_966,plain,
% 3.03/1.00      ( k1_xboole_0 = sK3
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3143,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3721,plain,
% 3.03/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_3143]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3805,plain,
% 3.03/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_3721]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3142,plain,( X0 = X0 ),theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3806,plain,
% 3.03/1.00      ( sK3 = sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_3142]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4263,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_4186,c_29,c_314,c_966,c_3805,c_3806]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_11,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_707,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k1_relat_1(X0) = X1
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_708,plain,
% 3.03/1.00      ( ~ r2_hidden(sK4,k1_funct_2(X0,X1))
% 3.03/1.00      | ~ v1_relat_1(sK4)
% 3.03/1.00      | k1_relat_1(sK4) = X0 ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_707]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3520,plain,
% 3.03/1.00      ( k1_relat_1(sK4) = X0
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_709,plain,
% 3.03/1.00      ( k1_relat_1(sK4) = X0
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4029,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top
% 3.03/1.00      | k1_relat_1(sK4) = X0 ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3520,c_29,c_709,c_3694]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4030,plain,
% 3.03/1.00      ( k1_relat_1(sK4) = X0
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X0,X1)) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_4029]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4270,plain,
% 3.03/1.00      ( k1_relat_1(sK4) = sK2 ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4263,c_4030]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4715,plain,
% 3.03/1.00      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_4464,c_4270]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_7,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | ~ m1_subset_1(X3,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | v1_xboole_0(X1)
% 3.03/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.03/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_24,negated_conjecture,
% 3.03/1.00      ( ~ v1_xboole_0(sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_343,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | ~ m1_subset_1(X3,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.03/1.00      | sK2 != X1 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_344,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.03/1.00      | ~ m1_subset_1(X2,sK2)
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_343]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_611,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.03/1.00      | ~ m1_subset_1(X2,sK2)
% 3.03/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_344,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_612,plain,
% 3.03/1.00      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.03/1.00      | ~ m1_subset_1(X1,sK2)
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.03/1.00      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_611]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3526,plain,
% 3.03/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.03/1.00      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.03/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4373,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.03/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.03/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3532,c_3526]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_928,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.03/1.00      | k3_funct_2(sK2,X1,sK4,X0) = k1_funct_1(sK4,X0)
% 3.03/1.00      | sK4 != sK4
% 3.03/1.00      | sK3 != X1
% 3.03/1.00      | sK2 != sK2 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_612]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_929,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.03/1.00      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_928]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_933,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.03/1.00      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_929,c_20]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_935,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.03/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4376,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.03/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_4373,c_935]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4721,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4715,c_4376]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3534,plain,
% 3.03/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.03/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4952,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4721,c_3534]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_19,negated_conjecture,
% 3.03/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.03/1.00      | ~ m1_subset_1(X0,sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3533,plain,
% 3.03/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
% 3.03/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5499,plain,
% 3.03/1.00      ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4952,c_3533]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_12,plain,
% 3.03/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_692,plain,
% 3.03/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_693,plain,
% 3.03/1.00      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.03/1.00      | ~ v1_relat_1(sK4) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_692]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3521,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_694,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4106,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3521,c_29,c_694,c_3694]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4107,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_4106]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4552,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_4270,c_4107]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5620,plain,
% 3.03/1.00      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.03/1.00      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5499,c_4552]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4955,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | k1_xboole_0 = X0
% 3.03/1.00      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4721,c_3519]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_15,plain,
% 3.03/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_647,plain,
% 3.03/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_648,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.03/1.00      | ~ v1_relat_1(sK4) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_647]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3524,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_649,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4443,plain,
% 3.03/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.03/1.00      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3524,c_29,c_649,c_3694]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4444,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_4443]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4451,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4444,c_3537]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4704,plain,
% 3.03/1.00      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_4451,c_4270]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4710,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | v1_funct_2(sK4,sK2,X0) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4704,c_4376]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5274,plain,
% 3.03/1.00      ( k1_xboole_0 = X0
% 3.03/1.00      | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_4955,c_4710]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5275,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.03/1.00      | k1_xboole_0 = X0
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,X0)) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_5274]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_10,plain,
% 3.03/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.03/1.00      | ~ r2_hidden(X0,k1_funct_2(X2,X1))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_18,negated_conjecture,
% 3.03/1.00      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_404,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 3.03/1.00      | sK1 != X2 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_405,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,k1_funct_2(X1,sK1))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_581,plain,
% 3.03/1.00      ( ~ r2_hidden(X0,k1_funct_2(X1,sK1))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_405,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_582,plain,
% 3.03/1.00      ( ~ r2_hidden(sK4,k1_funct_2(X0,sK1))
% 3.03/1.00      | ~ v1_relat_1(sK4)
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_581]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3139,plain,
% 3.03/1.00      ( ~ r2_hidden(sK4,k1_funct_2(X0,sK1)) | ~ sP0_iProver_split ),
% 3.03/1.00      inference(splitting,
% 3.03/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.03/1.00                [c_582]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3529,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top
% 3.03/1.00      | sP0_iProver_split != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3139]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_583,plain,
% 3.03/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3703,plain,
% 3.03/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3731,plain,
% 3.03/1.00      ( r2_hidden(sK4,k1_funct_2(X0,sK1)) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3529,c_20,c_29,c_583,c_3694,c_3703]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5284,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 3.03/1.00      | sK1 = k1_xboole_0 ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5275,c_3731]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5312,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5284,c_3533]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5549,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0
% 3.03/1.00      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5312,c_4552]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5716,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5549,c_4715]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5721,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0
% 3.03/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,sK1)) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5716,c_3519]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_585,plain,
% 3.03/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.03/1.00      | r2_hidden(sK4,k1_funct_2(sK2,sK1)) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_583]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_14,plain,
% 3.03/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.03/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_662,plain,
% 3.03/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.03/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | sK4 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_663,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.03/1.00      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.03/1.00      | ~ v1_relat_1(sK4) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_662]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3523,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_664,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4097,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 3.03/1.00      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3523,c_29,c_664,c_3694]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4098,plain,
% 3.03/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_4097]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4553,plain,
% 3.03/1.00      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.03/1.00      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_4270,c_4098]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5550,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0
% 3.03/1.00      | v1_funct_2(sK4,sK2,sK1) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5312,c_4553]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5640,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0 | v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5550,c_4704]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5745,plain,
% 3.03/1.00      ( sK1 = k1_xboole_0 ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5721,c_20,c_29,c_585,c_3694,c_3703,c_5640]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6182,plain,
% 3.03/1.00      ( k2_relset_1(sK2,k1_xboole_0,sK4) = k2_relat_1(sK4)
% 3.03/1.00      | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_5620,c_5745]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6186,plain,
% 3.03/1.00      ( k2_relset_1(sK2,k1_xboole_0,sK4) = k2_relat_1(sK4) ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_6182,c_3534,c_4715]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3535,plain,
% 3.03/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6187,plain,
% 3.03/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_6186,c_3535]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3831,plain,
% 3.03/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3532,c_3534]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3,plain,
% 3.03/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_185,plain,
% 3.03/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.03/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_397,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.03/1.00      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.03/1.00      | sK1 != X1 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_185,c_18]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_398,plain,
% 3.03/1.00      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3530,plain,
% 3.03/1.00      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3983,plain,
% 3.03/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3831,c_3530]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5750,plain,
% 3.03/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_5745,c_3983]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6493,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_6187,c_5750]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6498,plain,
% 3.03/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,k1_xboole_0,sK4)) = k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4)) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4721,c_6493]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5753,plain,
% 3.03/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),k1_xboole_0) = iProver_top
% 3.03/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_5745,c_3533]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6697,plain,
% 3.03/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4)),k1_xboole_0) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_6498,c_5753]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6773,plain,
% 3.03/1.00      ( v1_funct_2(sK4,sK2,k1_xboole_0) = iProver_top
% 3.03/1.00      | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_6697,c_4553]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6772,plain,
% 3.03/1.00      ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_6697,c_4552]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6785,plain,
% 3.03/1.00      ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_6773,c_5750,c_6187,c_6772]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6790,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_4715,c_6785]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(contradiction,plain,
% 3.03/1.00      ( $false ),
% 3.03/1.00      inference(minisat,[status(thm)],[c_6790,c_6187,c_5750]) ).
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  ------                               Statistics
% 3.03/1.00  
% 3.03/1.00  ------ General
% 3.03/1.00  
% 3.03/1.00  abstr_ref_over_cycles:                  0
% 3.03/1.00  abstr_ref_under_cycles:                 0
% 3.03/1.00  gc_basic_clause_elim:                   0
% 3.03/1.00  forced_gc_time:                         0
% 3.03/1.00  parsing_time:                           0.013
% 3.03/1.00  unif_index_cands_time:                  0.
% 3.03/1.00  unif_index_add_time:                    0.
% 3.03/1.00  orderings_time:                         0.
% 3.03/1.00  out_proof_time:                         0.012
% 3.03/1.00  total_time:                             0.193
% 3.03/1.00  num_of_symbols:                         53
% 3.03/1.00  num_of_terms:                           4595
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing
% 3.03/1.00  
% 3.03/1.00  num_of_splits:                          1
% 3.03/1.00  num_of_split_atoms:                     1
% 3.03/1.00  num_of_reused_defs:                     0
% 3.03/1.00  num_eq_ax_congr_red:                    12
% 3.03/1.00  num_of_sem_filtered_clauses:            1
% 3.03/1.00  num_of_subtypes:                        0
% 3.03/1.00  monotx_restored_types:                  0
% 3.03/1.00  sat_num_of_epr_types:                   0
% 3.03/1.00  sat_num_of_non_cyclic_types:            0
% 3.03/1.00  sat_guarded_non_collapsed_types:        0
% 3.03/1.00  num_pure_diseq_elim:                    0
% 3.03/1.00  simp_replaced_by:                       0
% 3.03/1.00  res_preprocessed:                       119
% 3.03/1.00  prep_upred:                             0
% 3.03/1.00  prep_unflattend:                        102
% 3.03/1.00  smt_new_axioms:                         0
% 3.03/1.00  pred_elim_cands:                        4
% 3.03/1.00  pred_elim:                              3
% 3.03/1.00  pred_elim_cl:                           2
% 3.03/1.00  pred_elim_cycles:                       10
% 3.03/1.00  merged_defs:                            2
% 3.03/1.00  merged_defs_ncl:                        0
% 3.03/1.00  bin_hyper_res:                          2
% 3.03/1.00  prep_cycles:                            4
% 3.03/1.00  pred_elim_time:                         0.052
% 3.03/1.00  splitting_time:                         0.
% 3.03/1.00  sem_filter_time:                        0.
% 3.03/1.00  monotx_time:                            0.
% 3.03/1.00  subtype_inf_time:                       0.
% 3.03/1.00  
% 3.03/1.00  ------ Problem properties
% 3.03/1.00  
% 3.03/1.00  clauses:                                22
% 3.03/1.00  conjectures:                            3
% 3.03/1.00  epr:                                    4
% 3.03/1.00  horn:                                   19
% 3.03/1.00  ground:                                 6
% 3.03/1.00  unary:                                  5
% 3.03/1.00  binary:                                 6
% 3.03/1.00  lits:                                   53
% 3.03/1.00  lits_eq:                                8
% 3.03/1.00  fd_pure:                                0
% 3.03/1.00  fd_pseudo:                              0
% 3.03/1.00  fd_cond:                                2
% 3.03/1.00  fd_pseudo_cond:                         0
% 3.03/1.00  ac_symbols:                             0
% 3.03/1.00  
% 3.03/1.00  ------ Propositional Solver
% 3.03/1.00  
% 3.03/1.00  prop_solver_calls:                      31
% 3.03/1.00  prop_fast_solver_calls:                 1459
% 3.03/1.00  smt_solver_calls:                       0
% 3.03/1.00  smt_fast_solver_calls:                  0
% 3.03/1.00  prop_num_of_clauses:                    1866
% 3.03/1.00  prop_preprocess_simplified:             5682
% 3.03/1.00  prop_fo_subsumed:                       47
% 3.03/1.00  prop_solver_time:                       0.
% 3.03/1.00  smt_solver_time:                        0.
% 3.03/1.00  smt_fast_solver_time:                   0.
% 3.03/1.00  prop_fast_solver_time:                  0.
% 3.03/1.00  prop_unsat_core_time:                   0.
% 3.03/1.00  
% 3.03/1.00  ------ QBF
% 3.03/1.00  
% 3.03/1.00  qbf_q_res:                              0
% 3.03/1.00  qbf_num_tautologies:                    0
% 3.03/1.00  qbf_prep_cycles:                        0
% 3.03/1.00  
% 3.03/1.00  ------ BMC1
% 3.03/1.00  
% 3.03/1.00  bmc1_current_bound:                     -1
% 3.03/1.00  bmc1_last_solved_bound:                 -1
% 3.03/1.00  bmc1_unsat_core_size:                   -1
% 3.03/1.00  bmc1_unsat_core_parents_size:           -1
% 3.03/1.00  bmc1_merge_next_fun:                    0
% 3.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation
% 3.03/1.00  
% 3.03/1.00  inst_num_of_clauses:                    471
% 3.03/1.00  inst_num_in_passive:                    143
% 3.03/1.00  inst_num_in_active:                     318
% 3.03/1.00  inst_num_in_unprocessed:                10
% 3.03/1.00  inst_num_of_loops:                      380
% 3.03/1.00  inst_num_of_learning_restarts:          0
% 3.03/1.00  inst_num_moves_active_passive:          55
% 3.03/1.00  inst_lit_activity:                      0
% 3.03/1.00  inst_lit_activity_moves:                0
% 3.03/1.00  inst_num_tautologies:                   0
% 3.03/1.00  inst_num_prop_implied:                  0
% 3.03/1.00  inst_num_existing_simplified:           0
% 3.03/1.00  inst_num_eq_res_simplified:             0
% 3.03/1.00  inst_num_child_elim:                    0
% 3.03/1.00  inst_num_of_dismatching_blockings:      115
% 3.03/1.00  inst_num_of_non_proper_insts:           518
% 3.03/1.00  inst_num_of_duplicates:                 0
% 3.03/1.00  inst_inst_num_from_inst_to_res:         0
% 3.03/1.00  inst_dismatching_checking_time:         0.
% 3.03/1.00  
% 3.03/1.00  ------ Resolution
% 3.03/1.00  
% 3.03/1.00  res_num_of_clauses:                     0
% 3.03/1.00  res_num_in_passive:                     0
% 3.03/1.00  res_num_in_active:                      0
% 3.03/1.00  res_num_of_loops:                       123
% 3.03/1.00  res_forward_subset_subsumed:            74
% 3.03/1.00  res_backward_subset_subsumed:           2
% 3.03/1.00  res_forward_subsumed:                   0
% 3.03/1.00  res_backward_subsumed:                  0
% 3.03/1.00  res_forward_subsumption_resolution:     16
% 3.03/1.00  res_backward_subsumption_resolution:    0
% 3.03/1.00  res_clause_to_clause_subsumption:       314
% 3.03/1.00  res_orphan_elimination:                 0
% 3.03/1.00  res_tautology_del:                      97
% 3.03/1.00  res_num_eq_res_simplified:              0
% 3.03/1.00  res_num_sel_changes:                    0
% 3.03/1.00  res_moves_from_active_to_pass:          0
% 3.03/1.00  
% 3.03/1.00  ------ Superposition
% 3.03/1.00  
% 3.03/1.00  sup_time_total:                         0.
% 3.03/1.00  sup_time_generating:                    0.
% 3.03/1.00  sup_time_sim_full:                      0.
% 3.03/1.00  sup_time_sim_immed:                     0.
% 3.03/1.00  
% 3.03/1.00  sup_num_of_clauses:                     82
% 3.03/1.00  sup_num_in_active:                      60
% 3.03/1.00  sup_num_in_passive:                     22
% 3.03/1.00  sup_num_of_loops:                       75
% 3.03/1.00  sup_fw_superposition:                   29
% 3.03/1.00  sup_bw_superposition:                   59
% 3.03/1.00  sup_immediate_simplified:               4
% 3.03/1.00  sup_given_eliminated:                   0
% 3.03/1.00  comparisons_done:                       0
% 3.03/1.00  comparisons_avoided:                    27
% 3.03/1.00  
% 3.03/1.00  ------ Simplifications
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  sim_fw_subset_subsumed:                 4
% 3.03/1.00  sim_bw_subset_subsumed:                 8
% 3.03/1.00  sim_fw_subsumed:                        0
% 3.03/1.00  sim_bw_subsumed:                        0
% 3.03/1.00  sim_fw_subsumption_res:                 5
% 3.03/1.00  sim_bw_subsumption_res:                 0
% 3.03/1.00  sim_tautology_del:                      0
% 3.03/1.00  sim_eq_tautology_del:                   4
% 3.03/1.00  sim_eq_res_simp:                        0
% 3.03/1.00  sim_fw_demodulated:                     0
% 3.03/1.00  sim_bw_demodulated:                     12
% 3.03/1.00  sim_light_normalised:                   5
% 3.03/1.00  sim_joinable_taut:                      0
% 3.03/1.00  sim_joinable_simp:                      0
% 3.03/1.00  sim_ac_normalised:                      0
% 3.03/1.00  sim_smt_subsumption:                    0
% 3.03/1.00  
%------------------------------------------------------------------------------
