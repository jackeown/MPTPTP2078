%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:15 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 376 expanded)
%              Number of clauses        :   66 ( 121 expanded)
%              Number of leaves         :   18 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  406 (1961 expanded)
%              Number of equality atoms :   39 (  44 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f33,f32,f31])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_194,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_194])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2489,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1,c_21])).

cnf(c_2672,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_237,c_2489])).

cnf(c_2350,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2441,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2501,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2727,plain,
    ( v1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2672,c_21,c_2350,c_2441,c_2501])).

cnf(c_13,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_499,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_500,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_2741,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2727,c_500])).

cnf(c_1661,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1656,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3388,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1661,c_1656])).

cnf(c_1657,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3152,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1657,c_1656])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_418,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_23])).

cnf(c_419,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_5353,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k1_funct_1(sK4,X1) = k3_funct_2(sK2,X0,sK4,X1) ),
    inference(resolution,[status(thm)],[c_3152,c_419])).

cnf(c_6704,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ r2_hidden(k3_funct_2(sK2,X0,sK4,X1),X2)
    | r2_hidden(k1_funct_1(sK4,X1),X2)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(resolution,[status(thm)],[c_3388,c_5353])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7336,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | r2_hidden(k1_funct_1(sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_6704,c_20])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7341,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7336,c_22,c_21])).

cnf(c_7342,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(renaming,[status(thm)],[c_7341])).

cnf(c_7571,plain,
    ( ~ m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
    inference(resolution,[status(thm)],[c_2741,c_7342])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_326,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_3033,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_326,c_21])).

cnf(c_2572,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_2701,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_3036,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_21,c_2350,c_2441,c_2501,c_2701])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2913,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | m1_subset_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_3136,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | m1_subset_1(X0,sK2) ),
    inference(resolution,[status(thm)],[c_3036,c_2913])).

cnf(c_14,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_484,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_485,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_2740,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2727,c_485])).

cnf(c_3401,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(resolution,[status(thm)],[c_3136,c_2740])).

cnf(c_7576,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7571,c_3401])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_345,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_8767,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_7576,c_345])).

cnf(c_2175,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2178,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2714,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2175,c_2178])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2177,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2823,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2714,c_2177])).

cnf(c_2824,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2823])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8767,c_2824,c_2501,c_2441,c_2350,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 18
% 3.48/0.99  conjectures                             4
% 3.48/0.99  EPR                                     2
% 3.48/0.99  Horn                                    16
% 3.48/0.99  unary                                   4
% 3.48/0.99  binary                                  4
% 3.48/0.99  lits                                    44
% 3.48/0.99  lits eq                                 3
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 0
% 3.48/0.99  fd_pseudo_cond                          0
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Input Options Time Limit: Unbounded
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status Theorem for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  fof(f3,axiom,(
% 3.48/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f15,plain,(
% 3.48/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.48/0.99    inference(ennf_transformation,[],[f3])).
% 3.48/0.99  
% 3.48/0.99  fof(f38,plain,(
% 3.48/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f15])).
% 3.48/0.99  
% 3.48/0.99  fof(f1,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f26,plain,(
% 3.48/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.48/0.99    inference(nnf_transformation,[],[f1])).
% 3.48/0.99  
% 3.48/0.99  fof(f36,plain,(
% 3.48/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f26])).
% 3.48/0.99  
% 3.48/0.99  fof(f35,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f26])).
% 3.48/0.99  
% 3.48/0.99  fof(f11,conjecture,(
% 3.48/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f12,negated_conjecture,(
% 3.48/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.48/0.99    inference(negated_conjecture,[],[f11])).
% 3.48/0.99  
% 3.48/0.99  fof(f24,plain,(
% 3.48/0.99    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.48/0.99    inference(ennf_transformation,[],[f12])).
% 3.48/0.99  
% 3.48/0.99  fof(f25,plain,(
% 3.48/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.48/0.99    inference(flattening,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f33,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f32,plain,(
% 3.48/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f31,plain,(
% 3.48/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f34,plain,(
% 3.48/0.99    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f33,f32,f31])).
% 3.48/0.99  
% 3.48/0.99  fof(f58,plain,(
% 3.48/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f6,axiom,(
% 3.48/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f43,plain,(
% 3.48/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f6])).
% 3.48/0.99  
% 3.48/0.99  fof(f10,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f22,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.48/0.99    inference(ennf_transformation,[],[f10])).
% 3.48/0.99  
% 3.48/0.99  fof(f23,plain,(
% 3.48/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.48/0.99    inference(flattening,[],[f22])).
% 3.48/0.99  
% 3.48/0.99  fof(f29,plain,(
% 3.48/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f30,plain,(
% 3.48/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).
% 3.48/0.99  
% 3.48/0.99  fof(f53,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f30])).
% 3.48/0.99  
% 3.48/0.99  fof(f61,plain,(
% 3.48/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.48/0.99    inference(equality_resolution,[],[f53])).
% 3.48/0.99  
% 3.48/0.99  fof(f56,plain,(
% 3.48/0.99    v1_funct_1(sK4)),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f9,axiom,(
% 3.48/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f20,plain,(
% 3.48/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f9])).
% 3.48/0.99  
% 3.48/0.99  fof(f21,plain,(
% 3.48/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.48/0.99    inference(flattening,[],[f20])).
% 3.48/0.99  
% 3.48/0.99  fof(f47,plain,(
% 3.48/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f21])).
% 3.48/0.99  
% 3.48/0.99  fof(f54,plain,(
% 3.48/0.99    ~v1_xboole_0(sK2)),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f59,plain,(
% 3.48/0.99    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f57,plain,(
% 3.48/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f7,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f18,plain,(
% 3.48/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/0.99    inference(ennf_transformation,[],[f7])).
% 3.48/0.99  
% 3.48/0.99  fof(f44,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f18])).
% 3.48/0.99  
% 3.48/0.99  fof(f4,axiom,(
% 3.48/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f16,plain,(
% 3.48/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.48/0.99    inference(ennf_transformation,[],[f4])).
% 3.48/0.99  
% 3.48/0.99  fof(f27,plain,(
% 3.48/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.48/0.99    inference(nnf_transformation,[],[f16])).
% 3.48/0.99  
% 3.48/0.99  fof(f39,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f27])).
% 3.48/0.99  
% 3.48/0.99  fof(f2,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f13,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.48/0.99    inference(ennf_transformation,[],[f2])).
% 3.48/0.99  
% 3.48/0.99  fof(f14,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.48/0.99    inference(flattening,[],[f13])).
% 3.48/0.99  
% 3.48/0.99  fof(f37,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f14])).
% 3.48/0.99  
% 3.48/0.99  fof(f52,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f30])).
% 3.48/0.99  
% 3.48/0.99  fof(f62,plain,(
% 3.48/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.48/0.99    inference(equality_resolution,[],[f52])).
% 3.48/0.99  
% 3.48/0.99  fof(f45,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f18])).
% 3.48/0.99  
% 3.48/0.99  fof(f5,axiom,(
% 3.48/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f17,plain,(
% 3.48/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.48/0.99    inference(ennf_transformation,[],[f5])).
% 3.48/0.99  
% 3.48/0.99  fof(f28,plain,(
% 3.48/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.48/0.99    inference(nnf_transformation,[],[f17])).
% 3.48/0.99  
% 3.48/0.99  fof(f41,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f28])).
% 3.48/0.99  
% 3.48/0.99  fof(f8,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f19,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/0.99    inference(ennf_transformation,[],[f8])).
% 3.48/0.99  
% 3.48/0.99  fof(f46,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f19])).
% 3.48/0.99  
% 3.48/0.99  fof(f60,plain,(
% 3.48/0.99    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | ~ v1_relat_1(X1)
% 3.48/0.99      | v1_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_0,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_194,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_237,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.48/0.99      inference(bin_hyper_res,[status(thm)],[c_3,c_194]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1,plain,
% 3.48/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_21,negated_conjecture,
% 3.48/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2489,plain,
% 3.48/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_1,c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2672,plain,
% 3.48/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) | v1_relat_1(sK4) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_237,c_2489]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2350,plain,
% 3.48/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2441,plain,
% 3.48/0.99      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
% 3.48/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 3.48/0.99      | v1_relat_1(sK4) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_237]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8,plain,
% 3.48/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2501,plain,
% 3.48/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2727,plain,
% 3.48/0.99      ( v1_relat_1(sK4) ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_2672,c_21,c_2350,c_2441,c_2501]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_13,plain,
% 3.48/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.48/0.99      | ~ v1_funct_1(X0)
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_23,negated_conjecture,
% 3.48/0.99      ( v1_funct_1(sK4) ),
% 3.48/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_499,plain,
% 3.48/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.48/0.99      | ~ v1_relat_1(X0)
% 3.48/0.99      | sK4 != X0 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_500,plain,
% 3.48/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.48/0.99      | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_499]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2741,plain,
% 3.48/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
% 3.48/0.99      inference(backward_subsumption_resolution,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_2727,c_500]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1661,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.48/0.99      theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1656,plain,( X0 = X0 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3388,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_1661,c_1656]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1657,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3152,plain,
% 3.48/0.99      ( X0 != X1 | X1 = X0 ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_1657,c_1656]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12,plain,
% 3.48/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/0.99      | ~ m1_subset_1(X3,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/0.99      | v1_xboole_0(X1)
% 3.48/0.99      | ~ v1_funct_1(X0)
% 3.48/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.48/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_25,negated_conjecture,
% 3.48/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_385,plain,
% 3.48/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/0.99      | ~ m1_subset_1(X3,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/0.99      | ~ v1_funct_1(X0)
% 3.48/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.48/0.99      | sK2 != X1 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_386,plain,
% 3.48/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.48/0.99      | ~ m1_subset_1(X2,sK2)
% 3.48/0.99      | ~ v1_funct_1(X0)
% 3.48/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_418,plain,
% 3.48/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.48/0.99      | ~ m1_subset_1(X2,sK2)
% 3.48/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.48/0.99      | sK4 != X0 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_386,c_23]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_419,plain,
% 3.48/0.99      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.48/0.99      | ~ m1_subset_1(X1,sK2)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.48/0.99      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5353,plain,
% 3.48/0.99      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.48/0.99      | ~ m1_subset_1(X1,sK2)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.48/0.99      | k1_funct_1(sK4,X1) = k3_funct_2(sK2,X0,sK4,X1) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_3152,c_419]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6704,plain,
% 3.48/0.99      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.48/0.99      | ~ r2_hidden(k3_funct_2(sK2,X0,sK4,X1),X2)
% 3.48/0.99      | r2_hidden(k1_funct_1(sK4,X1),X2)
% 3.48/0.99      | ~ m1_subset_1(X1,sK2)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_3388,c_5353]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_20,negated_conjecture,
% 3.48/0.99      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.48/0.99      | ~ m1_subset_1(X0,sK2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7336,plain,
% 3.48/0.99      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.48/0.99      | r2_hidden(k1_funct_1(sK4,X0),sK1)
% 3.48/0.99      | ~ m1_subset_1(X0,sK2)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_6704,c_20]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_22,negated_conjecture,
% 3.48/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.48/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7341,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,sK2) | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_7336,c_22,c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7342,plain,
% 3.48/0.99      ( r2_hidden(k1_funct_1(sK4,X0),sK1) | ~ m1_subset_1(X0,sK2) ),
% 3.48/0.99      inference(renaming,[status(thm)],[c_7341]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7571,plain,
% 3.48/0.99      ( ~ m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2)
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_2741,c_7342]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_10,plain,
% 3.48/0.99      ( v4_relat_1(X0,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5,plain,
% 3.48/0.99      ( ~ v4_relat_1(X0,X1)
% 3.48/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_326,plain,
% 3.48/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_10,c_5]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3033,plain,
% 3.48/0.99      ( r1_tarski(k1_relat_1(sK4),sK2) | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_326,c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2572,plain,
% 3.48/0.99      ( r1_tarski(k1_relat_1(sK4),X0)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/0.99      | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_326]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2701,plain,
% 3.48/0.99      ( r1_tarski(k1_relat_1(sK4),sK2)
% 3.48/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.48/0.99      | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_2572]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3036,plain,
% 3.48/0.99      ( r1_tarski(k1_relat_1(sK4),sK2) ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_3033,c_21,c_2350,c_2441,c_2501,c_2701]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,X1)
% 3.48/0.99      | m1_subset_1(X0,X2)
% 3.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2913,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | m1_subset_1(X0,X2) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3136,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4)) | m1_subset_1(X0,sK2) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_3036,c_2913]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_14,plain,
% 3.48/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.48/0.99      | ~ v1_funct_1(X0)
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_484,plain,
% 3.48/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.48/0.99      | ~ v1_relat_1(X0)
% 3.48/0.99      | sK4 != X0 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_485,plain,
% 3.48/0.99      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.48/0.99      | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2740,plain,
% 3.48/0.99      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
% 3.48/0.99      inference(backward_subsumption_resolution,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_2727,c_485]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3401,plain,
% 3.48/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2)
% 3.48/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_3136,c_2740]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7576,plain,
% 3.48/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
% 3.48/0.99      inference(forward_subsumption_resolution,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_7571,c_3401]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9,plain,
% 3.48/0.99      ( v5_relat_1(X0,X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7,plain,
% 3.48/0.99      ( ~ v5_relat_1(X0,X1)
% 3.48/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_345,plain,
% 3.48/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.48/0.99      | ~ v1_relat_1(X0) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8767,plain,
% 3.48/0.99      ( r1_tarski(k2_relat_1(sK4),sK1) | ~ v1_relat_1(sK4) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_7576,c_345]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2175,plain,
% 3.48/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_11,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2178,plain,
% 3.48/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.48/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2714,plain,
% 3.48/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2175,c_2178]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_19,negated_conjecture,
% 3.48/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2177,plain,
% 3.48/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2823,plain,
% 3.48/0.99      ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_2714,c_2177]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2824,plain,
% 3.48/0.99      ( ~ r1_tarski(k2_relat_1(sK4),sK1) ),
% 3.48/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2823]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(contradiction,plain,
% 3.48/0.99      ( $false ),
% 3.48/0.99      inference(minisat,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_8767,c_2824,c_2501,c_2441,c_2350,c_21]) ).
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  ------                               Statistics
% 3.48/0.99  
% 3.48/0.99  ------ Selected
% 3.48/0.99  
% 3.48/0.99  total_time:                             0.31
% 3.48/0.99  
%------------------------------------------------------------------------------
