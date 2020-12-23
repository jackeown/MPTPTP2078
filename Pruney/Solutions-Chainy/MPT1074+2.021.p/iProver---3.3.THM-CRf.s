%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:16 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  190 (5447 expanded)
%              Number of clauses        :  127 (1779 expanded)
%              Number of leaves         :   20 (1482 expanded)
%              Depth                    :   31
%              Number of atoms          :  618 (31989 expanded)
%              Number of equality atoms :  298 (4118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f37,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f36,f35,f34])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1214,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1222,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3440,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1222])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1229,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2293,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1214,c_1229])).

cnf(c_3444,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3440,c_2293])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3468,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_35])).

cnf(c_3469,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3468])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1217,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3473,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1217])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_262,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_209])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1594,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

cnf(c_1783,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_262,c_1594])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1917,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1783,c_8])).

cnf(c_1918,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1917])).

cnf(c_3753,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3473,c_34,c_1918])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1234,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3762,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3753,c_1234])).

cnf(c_20,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1219,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4196,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1219])).

cnf(c_5149,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4196,c_34,c_1918])).

cnf(c_5158,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_5149])).

cnf(c_5233,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5158,c_1234])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1221,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4460,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1221])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4626,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4460,c_32,c_34,c_35])).

cnf(c_6141,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5233,c_4626])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1228,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6402,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6141,c_1228])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1215,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7876,plain,
    ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_1215])).

cnf(c_19,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1220,plain,
    ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4447,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1220])).

cnf(c_5457,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4447,c_34,c_1918])).

cnf(c_8235,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7876,c_5457])).

cnf(c_8685,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_8235])).

cnf(c_9478,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8685,c_1228,c_5233])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9480,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9478,c_1230])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_40,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_535,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1693,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_537,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1532,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1692,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_2395,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_2396,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2395])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3222,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
    | r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_3223,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3222])).

cnf(c_11944,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9480,c_27,c_40,c_1524,c_1693,c_2396,c_3223])).

cnf(c_11951,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6141,c_11944])).

cnf(c_14045,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11951,c_1215])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1218,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3472,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1218])).

cnf(c_3767,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3472,c_34,c_1918])).

cnf(c_14066,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14045,c_3767])).

cnf(c_5163,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5149,c_1228])).

cnf(c_6133,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5163,c_1234])).

cnf(c_11941,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6133,c_4626])).

cnf(c_12744,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11941,c_1215])).

cnf(c_12768,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
    | sK3 = k1_xboole_0
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12744,c_6133])).

cnf(c_12769,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_12768])).

cnf(c_12778,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12769,c_5457])).

cnf(c_13902,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12778,c_1228])).

cnf(c_13905,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13902,c_1230])).

cnf(c_14065,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14045,c_5457])).

cnf(c_14190,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14066,c_27,c_40,c_1524,c_1693,c_2396,c_3223,c_13905,c_14065])).

cnf(c_14200,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3762,c_14190])).

cnf(c_1233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1232])).

cnf(c_7205,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_2403])).

cnf(c_13904,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13902,c_7205])).

cnf(c_5159,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5149,c_1232])).

cnf(c_5470,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_1234])).

cnf(c_14198,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5470,c_14190])).

cnf(c_15095,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14200,c_27,c_40,c_1524,c_1693,c_2396,c_13904,c_14198])).

cnf(c_2173,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1214,c_1228])).

cnf(c_2554,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_1230])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2792,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2554,c_36])).

cnf(c_2797,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2792,c_1232])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1237,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2801,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_1237])).

cnf(c_15128,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15095,c_2801])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4761,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4764,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4761])).

cnf(c_536,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4304,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK4)
    | k2_relat_1(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_4305,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4304])).

cnf(c_2387,plain,
    ( X0 != X1
    | k2_relset_1(sK2,sK3,sK4) != X1
    | k2_relset_1(sK2,sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_2893,plain,
    ( X0 != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = X0
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_2894,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_1859,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1695,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_104,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_99,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15128,c_4764,c_4305,c_2894,c_1859,c_1693,c_1695,c_1524,c_104,c_99,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 29
% 3.78/0.99  conjectures                             7
% 3.78/0.99  EPR                                     9
% 3.78/0.99  Horn                                    22
% 3.78/0.99  unary                                   9
% 3.78/0.99  binary                                  7
% 3.78/0.99  lits                                    72
% 3.78/0.99  lits eq                                 13
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 3
% 3.78/0.99  fd_pseudo_cond                          1
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Input Options Time Limit: Unbounded
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f13,conjecture,(
% 3.78/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f14,negated_conjecture,(
% 3.78/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.78/0.99    inference(negated_conjecture,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.78/0.99    inference(flattening,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f36,f35,f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f67,plain,(
% 3.78/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(flattening,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f50,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f31])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f66,plain,(
% 3.78/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f12,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.78/0.99    inference(ennf_transformation,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.78/0.99    inference(flattening,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f80,plain,(
% 3.78/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(equality_resolution,[],[f59])).
% 3.78/0.99  
% 3.78/0.99  fof(f65,plain,(
% 3.78/0.99    v1_funct_1(sK4)),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f16,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f44,plain,(
% 3.78/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f15,plain,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f61,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f78,plain,(
% 3.78/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(equality_resolution,[],[f61])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f56,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    ~v1_xboole_0(sK2)),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f68,plain,(
% 3.78/0.99    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f62,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f77,plain,(
% 3.78/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(equality_resolution,[],[f62])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f69,plain,(
% 3.78/0.99    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.78/0.99    inference(cnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f60,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f79,plain,(
% 3.78/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/0.99    inference(equality_resolution,[],[f60])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(flattening,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_27,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1214,plain,
% 3.78/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_17,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.78/0.99      | k1_xboole_0 = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1222,plain,
% 3.78/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.78/0.99      | k1_xboole_0 = X1
% 3.78/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3440,plain,
% 3.78/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1214,c_1222]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1229,plain,
% 3.78/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2293,plain,
% 3.78/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1214,c_1229]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3444,plain,
% 3.78/0.99      ( k1_relat_1(sK4) = sK2
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_3440,c_2293]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_28,negated_conjecture,
% 3.78/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_35,plain,
% 3.78/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3468,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_3444,c_35]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3469,plain,
% 3.78/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_3468]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,plain,
% 3.78/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.78/0.99      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1217,plain,
% 3.78/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 3.78/0.99      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3473,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | v1_funct_1(sK4) != iProver_top
% 3.78/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_1217]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_29,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK4) ),
% 3.78/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_34,plain,
% 3.78/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ v1_relat_1(X1)
% 3.78/0.99      | v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_208,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.78/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_209,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_208]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_262,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.78/0.99      inference(bin_hyper_res,[status(thm)],[c_7,c_209]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1594,plain,
% 3.78/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
% 3.78/0.99      inference(resolution,[status(thm)],[c_6,c_27]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1783,plain,
% 3.78/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) | v1_relat_1(sK4) ),
% 3.78/0.99      inference(resolution,[status(thm)],[c_262,c_1594]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8,plain,
% 3.78/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1917,plain,
% 3.78/0.99      ( v1_relat_1(sK4) ),
% 3.78/0.99      inference(forward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1783,c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1918,plain,
% 3.78/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1917]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3753,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_3473,c_34,c_1918]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1234,plain,
% 3.78/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3762,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3753,c_1234]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,plain,
% 3.78/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1219,plain,
% 3.78/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4196,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.78/0.99      | v1_funct_1(sK4) != iProver_top
% 3.78/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_1219]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5149,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4196,c_34,c_1918]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5158,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_5149]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5233,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5158,c_1234]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_18,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.99      | ~ m1_subset_1(X3,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | v1_xboole_0(X1)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1221,plain,
% 3.78/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.78/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | v1_xboole_0(X0) = iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4460,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.78/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,sK2) != iProver_top
% 3.78/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.78/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1214,c_1221]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_31,negated_conjecture,
% 3.78/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_32,plain,
% 3.78/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4626,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.78/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4460,c_32,c_34,c_35]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6141,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5233,c_4626]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1228,plain,
% 3.78/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6402,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.78/0.99      | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6141,c_1228]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_26,negated_conjecture,
% 3.78/0.99      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.78/0.99      | ~ m1_subset_1(X0,sK2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1215,plain,
% 3.78/0.99      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7876,plain,
% 3.78/0.99      ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6402,c_1215]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,plain,
% 3.78/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1220,plain,
% 3.78/0.99      ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4447,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.78/0.99      | v1_funct_1(sK4) != iProver_top
% 3.78/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_1220]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5457,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4447,c_34,c_1918]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8235,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_7876,c_5457]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8685,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_8235]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9478,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(forward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_8685,c_1228,c_5233]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1230,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9480,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_9478,c_1230]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_25,negated_conjecture,
% 3.78/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_40,plain,
% 3.78/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1524,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_535,plain,( X0 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1693,plain,
% 3.78/0.99      ( sK1 = sK1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_535]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_537,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1532,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1)
% 3.78/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.78/0.99      | sK1 != X1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1692,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,sK1)
% 3.78/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.78/0.99      | sK1 != sK1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1532]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2395,plain,
% 3.78/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.78/0.99      | ~ r1_tarski(k2_relat_1(sK4),sK1)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.78/0.99      | sK1 != sK1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1692]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2396,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.78/0.99      | sK1 != sK1
% 3.78/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2395]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1847,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) | r1_tarski(X0,sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3222,plain,
% 3.78/0.99      ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
% 3.78/0.99      | r1_tarski(k2_relat_1(sK4),sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1847]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3223,plain,
% 3.78/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3222]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11944,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_9480,c_27,c_40,c_1524,c_1693,c_2396,c_3223]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11951,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 3.78/0.99      | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6141,c_11944]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14045,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_11951,c_1215]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_21,plain,
% 3.78/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.78/0.99      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1218,plain,
% 3.78/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 3.78/0.99      | r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3472,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top
% 3.78/0.99      | v1_funct_1(sK4) != iProver_top
% 3.78/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3469,c_1218]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3767,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),X0) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_3472,c_34,c_1918]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14066,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_14045,c_3767]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5163,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5149,c_1228]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6133,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5163,c_1234]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11941,plain,
% 3.78/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.78/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_6133,c_4626]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12744,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_11941,c_1215]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12768,plain,
% 3.78/0.99      ( r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_12744,c_6133]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12769,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(k1_funct_1(sK4,sK0(sK2,X0,sK4)),sK1) = iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_12768]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12778,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_12769,c_5457]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13902,plain,
% 3.78/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 3.78/0.99      | sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(forward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_12778,c_1228]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13905,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_13902,c_1230]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14065,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_14045,c_5457]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14190,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_14066,c_27,c_40,c_1524,c_1693,c_2396,c_3223,c_13905,
% 3.78/0.99                 c_14065]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14200,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3762,c_14190]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1233,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1232,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2403,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1230,c_1232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7205,plain,
% 3.78/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1233,c_2403]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13904,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 3.78/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_13902,c_7205]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5159,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r2_hidden(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5149,c_1232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5470,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.78/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5159,c_1234]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14198,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0
% 3.78/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5470,c_14190]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15095,plain,
% 3.78/0.99      ( sK3 = k1_xboole_0 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_14200,c_27,c_40,c_1524,c_1693,c_2396,c_13904,c_14198]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2173,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1214,c_1228]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2554,plain,
% 3.78/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 3.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2173,c_1230]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_36,plain,
% 3.78/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2792,plain,
% 3.78/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_2554,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2797,plain,
% 3.78/0.99      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2792,c_1232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_0,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.78/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1237,plain,
% 3.78/0.99      ( X0 = X1
% 3.78/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.78/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2801,plain,
% 3.78/0.99      ( k2_relat_1(sK4) = sK3
% 3.78/0.99      | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2797,c_1237]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15128,plain,
% 3.78/0.99      ( k2_relat_1(sK4) = k1_xboole_0
% 3.78/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK4)) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_15095,c_2801]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3,plain,
% 3.78/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4761,plain,
% 3.78/0.99      ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4764,plain,
% 3.78/0.99      ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_4761]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_536,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4304,plain,
% 3.78/0.99      ( X0 != X1 | X0 = k2_relat_1(sK4) | k2_relat_1(sK4) != X1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4305,plain,
% 3.78/0.99      ( k2_relat_1(sK4) != k1_xboole_0
% 3.78/0.99      | k1_xboole_0 = k2_relat_1(sK4)
% 3.78/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_4304]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2387,plain,
% 3.78/0.99      ( X0 != X1
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != X1
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) = X0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2893,plain,
% 3.78/0.99      ( X0 != k2_relat_1(sK4)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) = X0
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2894,plain,
% 3.78/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) = k1_xboole_0
% 3.78/0.99      | k1_xboole_0 != k2_relat_1(sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2893]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1859,plain,
% 3.78/0.99      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1695,plain,
% 3.78/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.78/0.99      | ~ r1_tarski(k1_xboole_0,sK1)
% 3.78/0.99      | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
% 3.78/0.99      | sK1 != sK1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1692]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_104,plain,
% 3.78/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.78/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_99,plain,
% 3.78/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(contradiction,plain,
% 3.78/0.99      ( $false ),
% 3.78/0.99      inference(minisat,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_15128,c_4764,c_4305,c_2894,c_1859,c_1693,c_1695,
% 3.78/0.99                 c_1524,c_104,c_99,c_25,c_27]) ).
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  ------                               Statistics
% 3.78/0.99  
% 3.78/0.99  ------ Selected
% 3.78/0.99  
% 3.78/0.99  total_time:                             0.481
% 3.78/0.99  
%------------------------------------------------------------------------------
