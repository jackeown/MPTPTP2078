%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:17 EST 2020

% Result     : Theorem 27.30s
% Output     : CNFRefutation 27.30s
% Verified   : 
% Statistics : Number of formulae       :  225 (11019 expanded)
%              Number of clauses        :  156 (3612 expanded)
%              Number of leaves         :   21 (2950 expanded)
%              Depth                    :   39
%              Number of atoms          :  743 (66911 expanded)
%              Number of equality atoms :  343 (7626 expanded)
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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f39,f38,f37])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1505,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1506,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5652,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1506])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1513,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3190,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1505,c_1513])).

cnf(c_5683,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5652,c_3190])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6083,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5683,c_36])).

cnf(c_6084,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6083])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_498,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_499,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_619,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | m1_subset_1(X1,X2)
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X0,sK4) != X1
    | k1_relat_1(sK4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_499])).

cnf(c_620,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_1496,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_621,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1773,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_1877,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1894,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1895,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_3090,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_37,c_621,c_1877,c_1895])).

cnf(c_3091,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3090])).

cnf(c_6098,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_3091])).

cnf(c_21,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_528,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_529,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_604,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_529])).

cnf(c_605,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_1497,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_606,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_3600,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_37,c_606,c_1877,c_1895])).

cnf(c_3601,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3600])).

cnf(c_6096,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_3601])).

cnf(c_8289,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_6096])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_399,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_400,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_432,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_400,c_30])).

cnf(c_433,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1502,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_2021,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1502])).

cnf(c_2129,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2021,c_36])).

cnf(c_8707,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8289,c_2129])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1512,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8293,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6096,c_1512])).

cnf(c_28881,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8293,c_2129])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_513,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_514,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_652,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_514])).

cnf(c_653,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_653])).

cnf(c_1493,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_29843,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_28881,c_1493])).

cnf(c_29892,plain,
    ( sK3 = k1_xboole_0
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29843,c_8293])).

cnf(c_29893,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sK3 = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_29892])).

cnf(c_29902,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK3 = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_29893])).

cnf(c_30118,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_29902])).

cnf(c_20,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_543,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_544,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_544])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_972,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_635])).

cnf(c_1494,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_1018,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_2180,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_37,c_1018,c_1877,c_1895])).

cnf(c_2493,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2180,c_1512])).

cnf(c_83203,plain,
    ( sK3 = k1_xboole_0
    | k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30118,c_2493])).

cnf(c_83204,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_83203])).

cnf(c_83207,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6084,c_83204])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_84318,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_83207,c_1514])).

cnf(c_2491,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1505,c_1512])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_360,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1503,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_2636,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2491,c_1503])).

cnf(c_84436,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_84318,c_2636])).

cnf(c_84449,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8707,c_84436])).

cnf(c_592,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,sK3,sK4,X2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_1498,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_84509,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_84449,c_1498])).

cnf(c_1516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_relset_1(X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1516])).

cnf(c_4397,plain,
    ( v1_relat_1(k2_relset_1(k1_relat_1(sK4),sK1,sK4)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2180,c_3691])).

cnf(c_83209,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_83204,c_4397])).

cnf(c_83208,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_83204,c_1514])).

cnf(c_84329,plain,
    ( sK3 = k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_83209,c_37,c_1018,c_1877,c_1895,c_2636,c_83208])).

cnf(c_6116,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_1493])).

cnf(c_84507,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_84449,c_6116])).

cnf(c_84533,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_84509,c_84329,c_84507])).

cnf(c_84534,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_84533])).

cnf(c_84543,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_84534])).

cnf(c_84542,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8289,c_84534])).

cnf(c_84562,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_84543,c_2636,c_84318,c_84542])).

cnf(c_84981,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_84562,c_1505])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_84986,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_84981,c_0])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2495,plain,
    ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1512])).

cnf(c_85100,plain,
    ( k2_relset_1(k1_xboole_0,X0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_84986,c_2495])).

cnf(c_91539,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_85100,c_1514])).

cnf(c_91576,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91539,c_1])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_978,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_990,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_1791,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1792,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_342,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_30])).

cnf(c_469,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1500,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_1826,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1500])).

cnf(c_2417,plain,
    ( k1_zfmisc_1(sK3) = k1_zfmisc_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_2419,plain,
    ( k1_zfmisc_1(sK3) = k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_975,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2316,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK2,sK3,sK4)
    | k2_relset_1(sK2,sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_3525,plain,
    ( X0 = k2_relset_1(sK2,sK3,sK4)
    | X0 != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_3840,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = k2_relset_1(sK2,sK3,sK4)
    | k2_relat_1(sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3525])).

cnf(c_974,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3841,plain,
    ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1819,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | X0 != k2_relset_1(sK2,sK3,sK4)
    | X1 != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1975,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | X0 != k2_relset_1(sK2,sK3,sK4)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_6839,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0))
    | k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_6840,plain,
    ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6839])).

cnf(c_6842,plain,
    ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3)
    | m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6840])).

cnf(c_1973,plain,
    ( X0 != X1
    | X0 = k1_zfmisc_1(sK3)
    | k1_zfmisc_1(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_2416,plain,
    ( X0 != k1_zfmisc_1(X1)
    | X0 = k1_zfmisc_1(sK3)
    | k1_zfmisc_1(sK3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_6943,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3)
    | k1_zfmisc_1(sK3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_6944,plain,
    ( k1_zfmisc_1(sK3) != k1_zfmisc_1(k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6943])).

cnf(c_92637,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91576,c_28,c_37,c_103,c_104,c_990,c_1792,c_1797,c_1826,c_1877,c_1895,c_2419,c_2636,c_3840,c_3841,c_6842,c_6944,c_84318,c_84542])).

cnf(c_92656,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_92637,c_2636])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:04:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 27.30/3.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.30/3.98  
% 27.30/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.30/3.98  
% 27.30/3.98  ------  iProver source info
% 27.30/3.98  
% 27.30/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.30/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.30/3.98  git: non_committed_changes: false
% 27.30/3.98  git: last_make_outside_of_git: false
% 27.30/3.98  
% 27.30/3.98  ------ 
% 27.30/3.98  
% 27.30/3.98  ------ Input Options
% 27.30/3.98  
% 27.30/3.98  --out_options                           all
% 27.30/3.98  --tptp_safe_out                         true
% 27.30/3.98  --problem_path                          ""
% 27.30/3.98  --include_path                          ""
% 27.30/3.98  --clausifier                            res/vclausify_rel
% 27.30/3.98  --clausifier_options                    --mode clausify
% 27.30/3.98  --stdin                                 false
% 27.30/3.98  --stats_out                             all
% 27.30/3.98  
% 27.30/3.98  ------ General Options
% 27.30/3.98  
% 27.30/3.98  --fof                                   false
% 27.30/3.98  --time_out_real                         305.
% 27.30/3.98  --time_out_virtual                      -1.
% 27.30/3.98  --symbol_type_check                     false
% 27.30/3.98  --clausify_out                          false
% 27.30/3.98  --sig_cnt_out                           false
% 27.30/3.98  --trig_cnt_out                          false
% 27.30/3.98  --trig_cnt_out_tolerance                1.
% 27.30/3.98  --trig_cnt_out_sk_spl                   false
% 27.30/3.98  --abstr_cl_out                          false
% 27.30/3.98  
% 27.30/3.98  ------ Global Options
% 27.30/3.98  
% 27.30/3.98  --schedule                              default
% 27.30/3.98  --add_important_lit                     false
% 27.30/3.98  --prop_solver_per_cl                    1000
% 27.30/3.98  --min_unsat_core                        false
% 27.30/3.98  --soft_assumptions                      false
% 27.30/3.98  --soft_lemma_size                       3
% 27.30/3.98  --prop_impl_unit_size                   0
% 27.30/3.98  --prop_impl_unit                        []
% 27.30/3.98  --share_sel_clauses                     true
% 27.30/3.98  --reset_solvers                         false
% 27.30/3.98  --bc_imp_inh                            [conj_cone]
% 27.30/3.98  --conj_cone_tolerance                   3.
% 27.30/3.98  --extra_neg_conj                        none
% 27.30/3.98  --large_theory_mode                     true
% 27.30/3.98  --prolific_symb_bound                   200
% 27.30/3.98  --lt_threshold                          2000
% 27.30/3.98  --clause_weak_htbl                      true
% 27.30/3.98  --gc_record_bc_elim                     false
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing Options
% 27.30/3.98  
% 27.30/3.98  --preprocessing_flag                    true
% 27.30/3.98  --time_out_prep_mult                    0.1
% 27.30/3.98  --splitting_mode                        input
% 27.30/3.98  --splitting_grd                         true
% 27.30/3.98  --splitting_cvd                         false
% 27.30/3.98  --splitting_cvd_svl                     false
% 27.30/3.98  --splitting_nvd                         32
% 27.30/3.98  --sub_typing                            true
% 27.30/3.98  --prep_gs_sim                           true
% 27.30/3.98  --prep_unflatten                        true
% 27.30/3.98  --prep_res_sim                          true
% 27.30/3.98  --prep_upred                            true
% 27.30/3.98  --prep_sem_filter                       exhaustive
% 27.30/3.98  --prep_sem_filter_out                   false
% 27.30/3.98  --pred_elim                             true
% 27.30/3.98  --res_sim_input                         true
% 27.30/3.98  --eq_ax_congr_red                       true
% 27.30/3.98  --pure_diseq_elim                       true
% 27.30/3.98  --brand_transform                       false
% 27.30/3.98  --non_eq_to_eq                          false
% 27.30/3.98  --prep_def_merge                        true
% 27.30/3.98  --prep_def_merge_prop_impl              false
% 27.30/3.98  --prep_def_merge_mbd                    true
% 27.30/3.98  --prep_def_merge_tr_red                 false
% 27.30/3.98  --prep_def_merge_tr_cl                  false
% 27.30/3.98  --smt_preprocessing                     true
% 27.30/3.98  --smt_ac_axioms                         fast
% 27.30/3.98  --preprocessed_out                      false
% 27.30/3.98  --preprocessed_stats                    false
% 27.30/3.98  
% 27.30/3.98  ------ Abstraction refinement Options
% 27.30/3.98  
% 27.30/3.98  --abstr_ref                             []
% 27.30/3.98  --abstr_ref_prep                        false
% 27.30/3.98  --abstr_ref_until_sat                   false
% 27.30/3.98  --abstr_ref_sig_restrict                funpre
% 27.30/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.30/3.98  --abstr_ref_under                       []
% 27.30/3.98  
% 27.30/3.98  ------ SAT Options
% 27.30/3.98  
% 27.30/3.98  --sat_mode                              false
% 27.30/3.98  --sat_fm_restart_options                ""
% 27.30/3.98  --sat_gr_def                            false
% 27.30/3.98  --sat_epr_types                         true
% 27.30/3.98  --sat_non_cyclic_types                  false
% 27.30/3.98  --sat_finite_models                     false
% 27.30/3.98  --sat_fm_lemmas                         false
% 27.30/3.98  --sat_fm_prep                           false
% 27.30/3.98  --sat_fm_uc_incr                        true
% 27.30/3.98  --sat_out_model                         small
% 27.30/3.98  --sat_out_clauses                       false
% 27.30/3.98  
% 27.30/3.98  ------ QBF Options
% 27.30/3.98  
% 27.30/3.98  --qbf_mode                              false
% 27.30/3.98  --qbf_elim_univ                         false
% 27.30/3.98  --qbf_dom_inst                          none
% 27.30/3.98  --qbf_dom_pre_inst                      false
% 27.30/3.98  --qbf_sk_in                             false
% 27.30/3.98  --qbf_pred_elim                         true
% 27.30/3.98  --qbf_split                             512
% 27.30/3.98  
% 27.30/3.98  ------ BMC1 Options
% 27.30/3.98  
% 27.30/3.98  --bmc1_incremental                      false
% 27.30/3.98  --bmc1_axioms                           reachable_all
% 27.30/3.98  --bmc1_min_bound                        0
% 27.30/3.98  --bmc1_max_bound                        -1
% 27.30/3.98  --bmc1_max_bound_default                -1
% 27.30/3.98  --bmc1_symbol_reachability              true
% 27.30/3.98  --bmc1_property_lemmas                  false
% 27.30/3.98  --bmc1_k_induction                      false
% 27.30/3.98  --bmc1_non_equiv_states                 false
% 27.30/3.98  --bmc1_deadlock                         false
% 27.30/3.98  --bmc1_ucm                              false
% 27.30/3.98  --bmc1_add_unsat_core                   none
% 27.30/3.98  --bmc1_unsat_core_children              false
% 27.30/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.30/3.98  --bmc1_out_stat                         full
% 27.30/3.98  --bmc1_ground_init                      false
% 27.30/3.98  --bmc1_pre_inst_next_state              false
% 27.30/3.98  --bmc1_pre_inst_state                   false
% 27.30/3.98  --bmc1_pre_inst_reach_state             false
% 27.30/3.98  --bmc1_out_unsat_core                   false
% 27.30/3.98  --bmc1_aig_witness_out                  false
% 27.30/3.98  --bmc1_verbose                          false
% 27.30/3.98  --bmc1_dump_clauses_tptp                false
% 27.30/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.30/3.98  --bmc1_dump_file                        -
% 27.30/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.30/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.30/3.98  --bmc1_ucm_extend_mode                  1
% 27.30/3.98  --bmc1_ucm_init_mode                    2
% 27.30/3.98  --bmc1_ucm_cone_mode                    none
% 27.30/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.30/3.98  --bmc1_ucm_relax_model                  4
% 27.30/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.30/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.30/3.98  --bmc1_ucm_layered_model                none
% 27.30/3.98  --bmc1_ucm_max_lemma_size               10
% 27.30/3.98  
% 27.30/3.98  ------ AIG Options
% 27.30/3.98  
% 27.30/3.98  --aig_mode                              false
% 27.30/3.98  
% 27.30/3.98  ------ Instantiation Options
% 27.30/3.98  
% 27.30/3.98  --instantiation_flag                    true
% 27.30/3.98  --inst_sos_flag                         false
% 27.30/3.98  --inst_sos_phase                        true
% 27.30/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.30/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.30/3.98  --inst_lit_sel_side                     num_symb
% 27.30/3.98  --inst_solver_per_active                1400
% 27.30/3.98  --inst_solver_calls_frac                1.
% 27.30/3.98  --inst_passive_queue_type               priority_queues
% 27.30/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.30/3.98  --inst_passive_queues_freq              [25;2]
% 27.30/3.98  --inst_dismatching                      true
% 27.30/3.98  --inst_eager_unprocessed_to_passive     true
% 27.30/3.98  --inst_prop_sim_given                   true
% 27.30/3.98  --inst_prop_sim_new                     false
% 27.30/3.98  --inst_subs_new                         false
% 27.30/3.98  --inst_eq_res_simp                      false
% 27.30/3.98  --inst_subs_given                       false
% 27.30/3.98  --inst_orphan_elimination               true
% 27.30/3.98  --inst_learning_loop_flag               true
% 27.30/3.98  --inst_learning_start                   3000
% 27.30/3.98  --inst_learning_factor                  2
% 27.30/3.98  --inst_start_prop_sim_after_learn       3
% 27.30/3.98  --inst_sel_renew                        solver
% 27.30/3.98  --inst_lit_activity_flag                true
% 27.30/3.98  --inst_restr_to_given                   false
% 27.30/3.98  --inst_activity_threshold               500
% 27.30/3.98  --inst_out_proof                        true
% 27.30/3.98  
% 27.30/3.98  ------ Resolution Options
% 27.30/3.98  
% 27.30/3.98  --resolution_flag                       true
% 27.30/3.98  --res_lit_sel                           adaptive
% 27.30/3.98  --res_lit_sel_side                      none
% 27.30/3.98  --res_ordering                          kbo
% 27.30/3.98  --res_to_prop_solver                    active
% 27.30/3.98  --res_prop_simpl_new                    false
% 27.30/3.98  --res_prop_simpl_given                  true
% 27.30/3.98  --res_passive_queue_type                priority_queues
% 27.30/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.30/3.98  --res_passive_queues_freq               [15;5]
% 27.30/3.98  --res_forward_subs                      full
% 27.30/3.98  --res_backward_subs                     full
% 27.30/3.98  --res_forward_subs_resolution           true
% 27.30/3.98  --res_backward_subs_resolution          true
% 27.30/3.98  --res_orphan_elimination                true
% 27.30/3.98  --res_time_limit                        2.
% 27.30/3.98  --res_out_proof                         true
% 27.30/3.98  
% 27.30/3.98  ------ Superposition Options
% 27.30/3.98  
% 27.30/3.98  --superposition_flag                    true
% 27.30/3.98  --sup_passive_queue_type                priority_queues
% 27.30/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.30/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.30/3.98  --demod_completeness_check              fast
% 27.30/3.98  --demod_use_ground                      true
% 27.30/3.98  --sup_to_prop_solver                    passive
% 27.30/3.98  --sup_prop_simpl_new                    true
% 27.30/3.98  --sup_prop_simpl_given                  true
% 27.30/3.98  --sup_fun_splitting                     false
% 27.30/3.98  --sup_smt_interval                      50000
% 27.30/3.98  
% 27.30/3.98  ------ Superposition Simplification Setup
% 27.30/3.98  
% 27.30/3.98  --sup_indices_passive                   []
% 27.30/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.30/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_full_bw                           [BwDemod]
% 27.30/3.98  --sup_immed_triv                        [TrivRules]
% 27.30/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.30/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_immed_bw_main                     []
% 27.30/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.30/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.30/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.30/3.98  
% 27.30/3.98  ------ Combination Options
% 27.30/3.98  
% 27.30/3.98  --comb_res_mult                         3
% 27.30/3.98  --comb_sup_mult                         2
% 27.30/3.98  --comb_inst_mult                        10
% 27.30/3.98  
% 27.30/3.98  ------ Debug Options
% 27.30/3.98  
% 27.30/3.98  --dbg_backtrace                         false
% 27.30/3.98  --dbg_dump_prop_clauses                 false
% 27.30/3.98  --dbg_dump_prop_clauses_file            -
% 27.30/3.98  --dbg_out_stat                          false
% 27.30/3.98  ------ Parsing...
% 27.30/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.30/3.98  ------ Proving...
% 27.30/3.98  ------ Problem Properties 
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  clauses                                 36
% 27.30/3.98  conjectures                             2
% 27.30/3.98  EPR                                     1
% 27.30/3.98  Horn                                    23
% 27.30/3.98  unary                                   6
% 27.30/3.98  binary                                  4
% 27.30/3.98  lits                                    97
% 27.30/3.98  lits eq                                 24
% 27.30/3.98  fd_pure                                 0
% 27.30/3.98  fd_pseudo                               0
% 27.30/3.98  fd_cond                                 4
% 27.30/3.98  fd_pseudo_cond                          0
% 27.30/3.98  AC symbols                              0
% 27.30/3.98  
% 27.30/3.98  ------ Schedule dynamic 5 is on 
% 27.30/3.98  
% 27.30/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  ------ 
% 27.30/3.98  Current options:
% 27.30/3.98  ------ 
% 27.30/3.98  
% 27.30/3.98  ------ Input Options
% 27.30/3.98  
% 27.30/3.98  --out_options                           all
% 27.30/3.98  --tptp_safe_out                         true
% 27.30/3.98  --problem_path                          ""
% 27.30/3.98  --include_path                          ""
% 27.30/3.98  --clausifier                            res/vclausify_rel
% 27.30/3.98  --clausifier_options                    --mode clausify
% 27.30/3.98  --stdin                                 false
% 27.30/3.98  --stats_out                             all
% 27.30/3.98  
% 27.30/3.98  ------ General Options
% 27.30/3.98  
% 27.30/3.98  --fof                                   false
% 27.30/3.98  --time_out_real                         305.
% 27.30/3.98  --time_out_virtual                      -1.
% 27.30/3.98  --symbol_type_check                     false
% 27.30/3.98  --clausify_out                          false
% 27.30/3.98  --sig_cnt_out                           false
% 27.30/3.98  --trig_cnt_out                          false
% 27.30/3.98  --trig_cnt_out_tolerance                1.
% 27.30/3.98  --trig_cnt_out_sk_spl                   false
% 27.30/3.98  --abstr_cl_out                          false
% 27.30/3.98  
% 27.30/3.98  ------ Global Options
% 27.30/3.98  
% 27.30/3.98  --schedule                              default
% 27.30/3.98  --add_important_lit                     false
% 27.30/3.98  --prop_solver_per_cl                    1000
% 27.30/3.98  --min_unsat_core                        false
% 27.30/3.98  --soft_assumptions                      false
% 27.30/3.98  --soft_lemma_size                       3
% 27.30/3.98  --prop_impl_unit_size                   0
% 27.30/3.98  --prop_impl_unit                        []
% 27.30/3.98  --share_sel_clauses                     true
% 27.30/3.98  --reset_solvers                         false
% 27.30/3.98  --bc_imp_inh                            [conj_cone]
% 27.30/3.98  --conj_cone_tolerance                   3.
% 27.30/3.98  --extra_neg_conj                        none
% 27.30/3.98  --large_theory_mode                     true
% 27.30/3.98  --prolific_symb_bound                   200
% 27.30/3.98  --lt_threshold                          2000
% 27.30/3.98  --clause_weak_htbl                      true
% 27.30/3.98  --gc_record_bc_elim                     false
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing Options
% 27.30/3.98  
% 27.30/3.98  --preprocessing_flag                    true
% 27.30/3.98  --time_out_prep_mult                    0.1
% 27.30/3.98  --splitting_mode                        input
% 27.30/3.98  --splitting_grd                         true
% 27.30/3.98  --splitting_cvd                         false
% 27.30/3.98  --splitting_cvd_svl                     false
% 27.30/3.98  --splitting_nvd                         32
% 27.30/3.98  --sub_typing                            true
% 27.30/3.98  --prep_gs_sim                           true
% 27.30/3.98  --prep_unflatten                        true
% 27.30/3.98  --prep_res_sim                          true
% 27.30/3.98  --prep_upred                            true
% 27.30/3.98  --prep_sem_filter                       exhaustive
% 27.30/3.98  --prep_sem_filter_out                   false
% 27.30/3.98  --pred_elim                             true
% 27.30/3.98  --res_sim_input                         true
% 27.30/3.98  --eq_ax_congr_red                       true
% 27.30/3.98  --pure_diseq_elim                       true
% 27.30/3.98  --brand_transform                       false
% 27.30/3.98  --non_eq_to_eq                          false
% 27.30/3.98  --prep_def_merge                        true
% 27.30/3.98  --prep_def_merge_prop_impl              false
% 27.30/3.98  --prep_def_merge_mbd                    true
% 27.30/3.98  --prep_def_merge_tr_red                 false
% 27.30/3.98  --prep_def_merge_tr_cl                  false
% 27.30/3.98  --smt_preprocessing                     true
% 27.30/3.98  --smt_ac_axioms                         fast
% 27.30/3.98  --preprocessed_out                      false
% 27.30/3.98  --preprocessed_stats                    false
% 27.30/3.98  
% 27.30/3.98  ------ Abstraction refinement Options
% 27.30/3.98  
% 27.30/3.98  --abstr_ref                             []
% 27.30/3.98  --abstr_ref_prep                        false
% 27.30/3.98  --abstr_ref_until_sat                   false
% 27.30/3.98  --abstr_ref_sig_restrict                funpre
% 27.30/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.30/3.98  --abstr_ref_under                       []
% 27.30/3.98  
% 27.30/3.98  ------ SAT Options
% 27.30/3.98  
% 27.30/3.98  --sat_mode                              false
% 27.30/3.98  --sat_fm_restart_options                ""
% 27.30/3.98  --sat_gr_def                            false
% 27.30/3.98  --sat_epr_types                         true
% 27.30/3.98  --sat_non_cyclic_types                  false
% 27.30/3.98  --sat_finite_models                     false
% 27.30/3.98  --sat_fm_lemmas                         false
% 27.30/3.98  --sat_fm_prep                           false
% 27.30/3.98  --sat_fm_uc_incr                        true
% 27.30/3.98  --sat_out_model                         small
% 27.30/3.98  --sat_out_clauses                       false
% 27.30/3.98  
% 27.30/3.98  ------ QBF Options
% 27.30/3.98  
% 27.30/3.98  --qbf_mode                              false
% 27.30/3.98  --qbf_elim_univ                         false
% 27.30/3.98  --qbf_dom_inst                          none
% 27.30/3.98  --qbf_dom_pre_inst                      false
% 27.30/3.98  --qbf_sk_in                             false
% 27.30/3.98  --qbf_pred_elim                         true
% 27.30/3.98  --qbf_split                             512
% 27.30/3.98  
% 27.30/3.98  ------ BMC1 Options
% 27.30/3.98  
% 27.30/3.98  --bmc1_incremental                      false
% 27.30/3.98  --bmc1_axioms                           reachable_all
% 27.30/3.98  --bmc1_min_bound                        0
% 27.30/3.98  --bmc1_max_bound                        -1
% 27.30/3.98  --bmc1_max_bound_default                -1
% 27.30/3.98  --bmc1_symbol_reachability              true
% 27.30/3.98  --bmc1_property_lemmas                  false
% 27.30/3.98  --bmc1_k_induction                      false
% 27.30/3.98  --bmc1_non_equiv_states                 false
% 27.30/3.98  --bmc1_deadlock                         false
% 27.30/3.98  --bmc1_ucm                              false
% 27.30/3.98  --bmc1_add_unsat_core                   none
% 27.30/3.98  --bmc1_unsat_core_children              false
% 27.30/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.30/3.98  --bmc1_out_stat                         full
% 27.30/3.98  --bmc1_ground_init                      false
% 27.30/3.98  --bmc1_pre_inst_next_state              false
% 27.30/3.98  --bmc1_pre_inst_state                   false
% 27.30/3.98  --bmc1_pre_inst_reach_state             false
% 27.30/3.98  --bmc1_out_unsat_core                   false
% 27.30/3.98  --bmc1_aig_witness_out                  false
% 27.30/3.98  --bmc1_verbose                          false
% 27.30/3.98  --bmc1_dump_clauses_tptp                false
% 27.30/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.30/3.98  --bmc1_dump_file                        -
% 27.30/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.30/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.30/3.98  --bmc1_ucm_extend_mode                  1
% 27.30/3.98  --bmc1_ucm_init_mode                    2
% 27.30/3.98  --bmc1_ucm_cone_mode                    none
% 27.30/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.30/3.98  --bmc1_ucm_relax_model                  4
% 27.30/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.30/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.30/3.98  --bmc1_ucm_layered_model                none
% 27.30/3.98  --bmc1_ucm_max_lemma_size               10
% 27.30/3.98  
% 27.30/3.98  ------ AIG Options
% 27.30/3.98  
% 27.30/3.98  --aig_mode                              false
% 27.30/3.98  
% 27.30/3.98  ------ Instantiation Options
% 27.30/3.98  
% 27.30/3.98  --instantiation_flag                    true
% 27.30/3.98  --inst_sos_flag                         false
% 27.30/3.98  --inst_sos_phase                        true
% 27.30/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.30/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.30/3.98  --inst_lit_sel_side                     none
% 27.30/3.98  --inst_solver_per_active                1400
% 27.30/3.98  --inst_solver_calls_frac                1.
% 27.30/3.98  --inst_passive_queue_type               priority_queues
% 27.30/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.30/3.98  --inst_passive_queues_freq              [25;2]
% 27.30/3.98  --inst_dismatching                      true
% 27.30/3.98  --inst_eager_unprocessed_to_passive     true
% 27.30/3.98  --inst_prop_sim_given                   true
% 27.30/3.98  --inst_prop_sim_new                     false
% 27.30/3.98  --inst_subs_new                         false
% 27.30/3.98  --inst_eq_res_simp                      false
% 27.30/3.98  --inst_subs_given                       false
% 27.30/3.98  --inst_orphan_elimination               true
% 27.30/3.98  --inst_learning_loop_flag               true
% 27.30/3.98  --inst_learning_start                   3000
% 27.30/3.98  --inst_learning_factor                  2
% 27.30/3.98  --inst_start_prop_sim_after_learn       3
% 27.30/3.98  --inst_sel_renew                        solver
% 27.30/3.98  --inst_lit_activity_flag                true
% 27.30/3.98  --inst_restr_to_given                   false
% 27.30/3.98  --inst_activity_threshold               500
% 27.30/3.98  --inst_out_proof                        true
% 27.30/3.98  
% 27.30/3.98  ------ Resolution Options
% 27.30/3.98  
% 27.30/3.98  --resolution_flag                       false
% 27.30/3.98  --res_lit_sel                           adaptive
% 27.30/3.98  --res_lit_sel_side                      none
% 27.30/3.98  --res_ordering                          kbo
% 27.30/3.98  --res_to_prop_solver                    active
% 27.30/3.98  --res_prop_simpl_new                    false
% 27.30/3.98  --res_prop_simpl_given                  true
% 27.30/3.98  --res_passive_queue_type                priority_queues
% 27.30/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.30/3.98  --res_passive_queues_freq               [15;5]
% 27.30/3.98  --res_forward_subs                      full
% 27.30/3.98  --res_backward_subs                     full
% 27.30/3.98  --res_forward_subs_resolution           true
% 27.30/3.98  --res_backward_subs_resolution          true
% 27.30/3.98  --res_orphan_elimination                true
% 27.30/3.98  --res_time_limit                        2.
% 27.30/3.98  --res_out_proof                         true
% 27.30/3.98  
% 27.30/3.98  ------ Superposition Options
% 27.30/3.98  
% 27.30/3.98  --superposition_flag                    true
% 27.30/3.98  --sup_passive_queue_type                priority_queues
% 27.30/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.30/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.30/3.98  --demod_completeness_check              fast
% 27.30/3.98  --demod_use_ground                      true
% 27.30/3.98  --sup_to_prop_solver                    passive
% 27.30/3.98  --sup_prop_simpl_new                    true
% 27.30/3.98  --sup_prop_simpl_given                  true
% 27.30/3.98  --sup_fun_splitting                     false
% 27.30/3.98  --sup_smt_interval                      50000
% 27.30/3.98  
% 27.30/3.98  ------ Superposition Simplification Setup
% 27.30/3.98  
% 27.30/3.98  --sup_indices_passive                   []
% 27.30/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.30/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.30/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_full_bw                           [BwDemod]
% 27.30/3.98  --sup_immed_triv                        [TrivRules]
% 27.30/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.30/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_immed_bw_main                     []
% 27.30/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.30/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.30/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.30/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.30/3.98  
% 27.30/3.98  ------ Combination Options
% 27.30/3.98  
% 27.30/3.98  --comb_res_mult                         3
% 27.30/3.98  --comb_sup_mult                         2
% 27.30/3.98  --comb_inst_mult                        10
% 27.30/3.98  
% 27.30/3.98  ------ Debug Options
% 27.30/3.98  
% 27.30/3.98  --dbg_backtrace                         false
% 27.30/3.98  --dbg_dump_prop_clauses                 false
% 27.30/3.98  --dbg_dump_prop_clauses_file            -
% 27.30/3.98  --dbg_out_stat                          false
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  ------ Proving...
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  % SZS status Theorem for theBenchmark.p
% 27.30/3.98  
% 27.30/3.98   Resolution empty clause
% 27.30/3.98  
% 27.30/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.30/3.98  
% 27.30/3.98  fof(f13,conjecture,(
% 27.30/3.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f14,negated_conjecture,(
% 27.30/3.98    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 27.30/3.98    inference(negated_conjecture,[],[f13])).
% 27.30/3.98  
% 27.30/3.98  fof(f30,plain,(
% 27.30/3.98    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 27.30/3.98    inference(ennf_transformation,[],[f14])).
% 27.30/3.98  
% 27.30/3.98  fof(f31,plain,(
% 27.30/3.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 27.30/3.98    inference(flattening,[],[f30])).
% 27.30/3.98  
% 27.30/3.98  fof(f39,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 27.30/3.98    introduced(choice_axiom,[])).
% 27.30/3.98  
% 27.30/3.98  fof(f38,plain,(
% 27.30/3.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 27.30/3.98    introduced(choice_axiom,[])).
% 27.30/3.98  
% 27.30/3.98  fof(f37,plain,(
% 27.30/3.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 27.30/3.98    introduced(choice_axiom,[])).
% 27.30/3.98  
% 27.30/3.98  fof(f40,plain,(
% 27.30/3.98    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 27.30/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f39,f38,f37])).
% 27.30/3.98  
% 27.30/3.98  fof(f71,plain,(
% 27.30/3.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f9,axiom,(
% 27.30/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f22,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(ennf_transformation,[],[f9])).
% 27.30/3.98  
% 27.30/3.98  fof(f23,plain,(
% 27.30/3.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(flattening,[],[f22])).
% 27.30/3.98  
% 27.30/3.98  fof(f34,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(nnf_transformation,[],[f23])).
% 27.30/3.98  
% 27.30/3.98  fof(f51,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f34])).
% 27.30/3.98  
% 27.30/3.98  fof(f7,axiom,(
% 27.30/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f20,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(ennf_transformation,[],[f7])).
% 27.30/3.98  
% 27.30/3.98  fof(f49,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f20])).
% 27.30/3.98  
% 27.30/3.98  fof(f70,plain,(
% 27.30/3.98    v1_funct_2(sK4,sK2,sK3)),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f2,axiom,(
% 27.30/3.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f16,plain,(
% 27.30/3.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 27.30/3.98    inference(ennf_transformation,[],[f2])).
% 27.30/3.98  
% 27.30/3.98  fof(f44,plain,(
% 27.30/3.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f16])).
% 27.30/3.98  
% 27.30/3.98  fof(f12,axiom,(
% 27.30/3.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f28,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 27.30/3.98    inference(ennf_transformation,[],[f12])).
% 27.30/3.98  
% 27.30/3.98  fof(f29,plain,(
% 27.30/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.30/3.98    inference(flattening,[],[f28])).
% 27.30/3.98  
% 27.30/3.98  fof(f35,plain,(
% 27.30/3.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 27.30/3.98    introduced(choice_axiom,[])).
% 27.30/3.98  
% 27.30/3.98  fof(f36,plain,(
% 27.30/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.30/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f35])).
% 27.30/3.98  
% 27.30/3.98  fof(f63,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f36])).
% 27.30/3.98  
% 27.30/3.98  fof(f84,plain,(
% 27.30/3.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(equality_resolution,[],[f63])).
% 27.30/3.98  
% 27.30/3.98  fof(f69,plain,(
% 27.30/3.98    v1_funct_1(sK4)),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f4,axiom,(
% 27.30/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f18,plain,(
% 27.30/3.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.30/3.98    inference(ennf_transformation,[],[f4])).
% 27.30/3.98  
% 27.30/3.98  fof(f46,plain,(
% 27.30/3.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f18])).
% 27.30/3.98  
% 27.30/3.98  fof(f5,axiom,(
% 27.30/3.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f47,plain,(
% 27.30/3.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f5])).
% 27.30/3.98  
% 27.30/3.98  fof(f65,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f36])).
% 27.30/3.98  
% 27.30/3.98  fof(f82,plain,(
% 27.30/3.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(equality_resolution,[],[f65])).
% 27.30/3.98  
% 27.30/3.98  fof(f10,axiom,(
% 27.30/3.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f24,plain,(
% 27.30/3.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 27.30/3.98    inference(ennf_transformation,[],[f10])).
% 27.30/3.98  
% 27.30/3.98  fof(f25,plain,(
% 27.30/3.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 27.30/3.98    inference(flattening,[],[f24])).
% 27.30/3.98  
% 27.30/3.98  fof(f57,plain,(
% 27.30/3.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f25])).
% 27.30/3.98  
% 27.30/3.98  fof(f67,plain,(
% 27.30/3.98    ~v1_xboole_0(sK2)),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f8,axiom,(
% 27.30/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f21,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(ennf_transformation,[],[f8])).
% 27.30/3.98  
% 27.30/3.98  fof(f50,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f21])).
% 27.30/3.98  
% 27.30/3.98  fof(f72,plain,(
% 27.30/3.98    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f64,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f36])).
% 27.30/3.98  
% 27.30/3.98  fof(f83,plain,(
% 27.30/3.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(equality_resolution,[],[f64])).
% 27.30/3.98  
% 27.30/3.98  fof(f66,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f36])).
% 27.30/3.98  
% 27.30/3.98  fof(f81,plain,(
% 27.30/3.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.30/3.98    inference(equality_resolution,[],[f66])).
% 27.30/3.98  
% 27.30/3.98  fof(f6,axiom,(
% 27.30/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f19,plain,(
% 27.30/3.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.30/3.98    inference(ennf_transformation,[],[f6])).
% 27.30/3.98  
% 27.30/3.98  fof(f48,plain,(
% 27.30/3.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f19])).
% 27.30/3.98  
% 27.30/3.98  fof(f3,axiom,(
% 27.30/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f15,plain,(
% 27.30/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 27.30/3.98    inference(unused_predicate_definition_removal,[],[f3])).
% 27.30/3.98  
% 27.30/3.98  fof(f17,plain,(
% 27.30/3.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 27.30/3.98    inference(ennf_transformation,[],[f15])).
% 27.30/3.98  
% 27.30/3.98  fof(f45,plain,(
% 27.30/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.30/3.98    inference(cnf_transformation,[],[f17])).
% 27.30/3.98  
% 27.30/3.98  fof(f73,plain,(
% 27.30/3.98    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 27.30/3.98    inference(cnf_transformation,[],[f40])).
% 27.30/3.98  
% 27.30/3.98  fof(f1,axiom,(
% 27.30/3.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f32,plain,(
% 27.30/3.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 27.30/3.98    inference(nnf_transformation,[],[f1])).
% 27.30/3.98  
% 27.30/3.98  fof(f33,plain,(
% 27.30/3.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 27.30/3.98    inference(flattening,[],[f32])).
% 27.30/3.98  
% 27.30/3.98  fof(f43,plain,(
% 27.30/3.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 27.30/3.98    inference(cnf_transformation,[],[f33])).
% 27.30/3.98  
% 27.30/3.98  fof(f74,plain,(
% 27.30/3.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.30/3.98    inference(equality_resolution,[],[f43])).
% 27.30/3.98  
% 27.30/3.98  fof(f42,plain,(
% 27.30/3.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 27.30/3.98    inference(cnf_transformation,[],[f33])).
% 27.30/3.98  
% 27.30/3.98  fof(f75,plain,(
% 27.30/3.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 27.30/3.98    inference(equality_resolution,[],[f42])).
% 27.30/3.98  
% 27.30/3.98  fof(f41,plain,(
% 27.30/3.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 27.30/3.98    inference(cnf_transformation,[],[f33])).
% 27.30/3.98  
% 27.30/3.98  fof(f11,axiom,(
% 27.30/3.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 27.30/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.30/3.98  
% 27.30/3.98  fof(f26,plain,(
% 27.30/3.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.30/3.98    inference(ennf_transformation,[],[f11])).
% 27.30/3.98  
% 27.30/3.98  fof(f27,plain,(
% 27.30/3.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.30/3.98    inference(flattening,[],[f26])).
% 27.30/3.98  
% 27.30/3.98  fof(f60,plain,(
% 27.30/3.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.30/3.98    inference(cnf_transformation,[],[f27])).
% 27.30/3.98  
% 27.30/3.98  cnf(c_28,negated_conjecture,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 27.30/3.98      inference(cnf_transformation,[],[f71]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1505,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_15,plain,
% 27.30/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 27.30/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | k1_relset_1(X1,X2,X0) = X1
% 27.30/3.98      | k1_xboole_0 = X2 ),
% 27.30/3.98      inference(cnf_transformation,[],[f51]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1506,plain,
% 27.30/3.98      ( k1_relset_1(X0,X1,X2) = X0
% 27.30/3.98      | k1_xboole_0 = X1
% 27.30/3.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 27.30/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_5652,plain,
% 27.30/3.98      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1505,c_1506]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_8,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f49]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1513,plain,
% 27.30/3.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 27.30/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3190,plain,
% 27.30/3.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1505,c_1513]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_5683,plain,
% 27.30/3.98      ( k1_relat_1(sK4) = sK2
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 27.30/3.98      inference(demodulation,[status(thm)],[c_5652,c_3190]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_29,negated_conjecture,
% 27.30/3.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 27.30/3.98      inference(cnf_transformation,[],[f70]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_36,plain,
% 27.30/3.98      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6083,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 27.30/3.98      inference(global_propositional_subsumption,[status(thm)],[c_5683,c_36]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6084,plain,
% 27.30/3.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_6083]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3,plain,
% 27.30/3.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 27.30/3.98      inference(cnf_transformation,[],[f44]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_23,plain,
% 27.30/3.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 27.30/3.98      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f84]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_30,negated_conjecture,
% 27.30/3.98      ( v1_funct_1(sK4) ),
% 27.30/3.98      inference(cnf_transformation,[],[f69]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_498,plain,
% 27.30/3.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 27.30/3.98      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 27.30/3.98      | ~ v1_relat_1(X0)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_499,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 27.30/3.98      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_498]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_619,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 27.30/3.98      | m1_subset_1(X1,X2)
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | sK0(k1_relat_1(sK4),X0,sK4) != X1
% 27.30/3.98      | k1_relat_1(sK4) != X2 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_3,c_499]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_620,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 27.30/3.98      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_619]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1496,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 27.30/3.98      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_37,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_621,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 27.30/3.98      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_5,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f46]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1773,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | v1_relat_1(X0)
% 27.30/3.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_5]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1876,plain,
% 27.30/3.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 27.30/3.98      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 27.30/3.98      | v1_relat_1(sK4) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_1773]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1877,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 27.30/3.98      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 27.30/3.98      | v1_relat_1(sK4) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6,plain,
% 27.30/3.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.30/3.98      inference(cnf_transformation,[],[f47]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1894,plain,
% 27.30/3.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_6]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1895,plain,
% 27.30/3.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3090,plain,
% 27.30/3.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_1496,c_37,c_621,c_1877,c_1895]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3091,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 27.30/3.98      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_3090]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6098,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 27.30/3.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_3091]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_21,plain,
% 27.30/3.98      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 27.30/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f82]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_528,plain,
% 27.30/3.98      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 27.30/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ v1_relat_1(X0)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_529,plain,
% 27.30/3.98      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_528]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_604,plain,
% 27.30/3.98      ( m1_subset_1(X0,X1)
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 27.30/3.98      | k1_relat_1(sK4) != X1 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_3,c_529]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_605,plain,
% 27.30/3.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_604]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1497,plain,
% 27.30/3.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_606,plain,
% 27.30/3.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3600,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 27.30/3.98      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_1497,c_37,c_606,c_1877,c_1895]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3601,plain,
% 27.30/3.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_3600]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6096,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_3601]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_8289,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_6096]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_16,plain,
% 27.30/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 27.30/3.98      | ~ m1_subset_1(X3,X1)
% 27.30/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | v1_xboole_0(X1)
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 27.30/3.98      inference(cnf_transformation,[],[f57]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_32,negated_conjecture,
% 27.30/3.98      ( ~ v1_xboole_0(sK2) ),
% 27.30/3.98      inference(cnf_transformation,[],[f67]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_399,plain,
% 27.30/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 27.30/3.98      | ~ m1_subset_1(X3,X1)
% 27.30/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 27.30/3.98      | sK2 != X1 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_400,plain,
% 27.30/3.98      ( ~ v1_funct_2(X0,sK2,X1)
% 27.30/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 27.30/3.98      | ~ m1_subset_1(X2,sK2)
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_399]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_432,plain,
% 27.30/3.98      ( ~ v1_funct_2(X0,sK2,X1)
% 27.30/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 27.30/3.98      | ~ m1_subset_1(X2,sK2)
% 27.30/3.98      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_400,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_433,plain,
% 27.30/3.98      ( ~ v1_funct_2(sK4,sK2,X0)
% 27.30/3.98      | ~ m1_subset_1(X1,sK2)
% 27.30/3.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 27.30/3.98      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_432]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1502,plain,
% 27.30/3.98      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 27.30/3.98      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 27.30/3.98      | m1_subset_1(X1,sK2) != iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2021,plain,
% 27.30/3.98      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 27.30/3.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 27.30/3.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1505,c_1502]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2129,plain,
% 27.30/3.98      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 27.30/3.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,[status(thm)],[c_2021,c_36]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_8707,plain,
% 27.30/3.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_8289,c_2129]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_9,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f50]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1512,plain,
% 27.30/3.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 27.30/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_8293,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6096,c_1512]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_28881,plain,
% 27.30/3.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 27.30/3.98      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_8293,c_2129]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_27,negated_conjecture,
% 27.30/3.98      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) | ~ m1_subset_1(X0,sK2) ),
% 27.30/3.98      inference(cnf_transformation,[],[f72]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_22,plain,
% 27.30/3.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 27.30/3.98      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f83]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_513,plain,
% 27.30/3.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 27.30/3.98      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 27.30/3.98      | ~ v1_relat_1(X0)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_514,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 27.30/3.98      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_513]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_652,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 27.30/3.98      | ~ m1_subset_1(X1,sK2)
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 27.30/3.98      | sK1 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_27,c_514]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_653,plain,
% 27.30/3.98      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 27.30/3.98      | ~ m1_subset_1(X0,sK2)
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_652]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_970,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,sK2)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 27.30/3.98      | ~ sP2_iProver_split ),
% 27.30/3.98      inference(splitting,
% 27.30/3.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 27.30/3.98                [c_653]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1493,plain,
% 27.30/3.98      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 27.30/3.98      | m1_subset_1(X0,sK2) != iProver_top
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_29843,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_28881,c_1493]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_29892,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 27.30/3.98      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_29843,c_8293]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_29893,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_29892]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_29902,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_29893]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_30118,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(equality_resolution,[status(thm)],[c_29902]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_20,plain,
% 27.30/3.98      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 27.30/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f81]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_543,plain,
% 27.30/3.98      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 27.30/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ v1_relat_1(X0)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_544,plain,
% 27.30/3.98      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_543]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_634,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,sK2)
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 27.30/3.98      | sK1 != X1 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_27,c_544]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_635,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,sK2)
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_634]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_972,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 27.30/3.98      | ~ v1_relat_1(sK4)
% 27.30/3.98      | sP2_iProver_split ),
% 27.30/3.98      inference(splitting,
% 27.30/3.98                [splitting(split),new_symbols(definition,[])],
% 27.30/3.98                [c_635]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1494,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1018,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2180,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_1494,c_37,c_1018,c_1877,c_1895]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2493,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_2180,c_1512]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_83203,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_30118,c_2493]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_83204,plain,
% 27.30/3.98      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 27.30/3.98      | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_83203]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_83207,plain,
% 27.30/3.98      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_83204]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_7,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.30/3.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 27.30/3.98      inference(cnf_transformation,[],[f48]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1514,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.30/3.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84318,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_83207,c_1514]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2491,plain,
% 27.30/3.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1505,c_1512]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_4,plain,
% 27.30/3.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.30/3.98      inference(cnf_transformation,[],[f45]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_26,negated_conjecture,
% 27.30/3.98      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 27.30/3.98      inference(cnf_transformation,[],[f73]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_359,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.30/3.98      | k2_relset_1(sK2,sK3,sK4) != X0
% 27.30/3.98      | sK1 != X1 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_360,plain,
% 27.30/3.98      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_359]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1503,plain,
% 27.30/3.98      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2636,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 27.30/3.98      inference(demodulation,[status(thm)],[c_2491,c_1503]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84436,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_84318,c_2636]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84449,plain,
% 27.30/3.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 27.30/3.98      | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_8707,c_84436]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_592,plain,
% 27.30/3.98      ( m1_subset_1(X0,X1)
% 27.30/3.98      | ~ m1_subset_1(X2,sK2)
% 27.30/3.98      | k3_funct_2(sK2,sK3,sK4,X2) != X0
% 27.30/3.98      | sK1 != X1 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_593,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,sK2) | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_592]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1498,plain,
% 27.30/3.98      ( m1_subset_1(X0,sK2) != iProver_top
% 27.30/3.98      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84509,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 27.30/3.98      | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_84449,c_1498]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1516,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.30/3.98      | v1_relat_1(X1) != iProver_top
% 27.30/3.98      | v1_relat_1(X0) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3691,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.30/3.98      | v1_relat_1(X2) != iProver_top
% 27.30/3.98      | v1_relat_1(k2_relset_1(X1,X2,X0)) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1514,c_1516]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_4397,plain,
% 27.30/3.98      ( v1_relat_1(k2_relset_1(k1_relat_1(sK4),sK1,sK4)) = iProver_top
% 27.30/3.98      | v1_relat_1(sK1) != iProver_top
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_2180,c_3691]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_83209,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | v1_relat_1(k2_relat_1(sK4)) = iProver_top
% 27.30/3.98      | v1_relat_1(sK1) != iProver_top
% 27.30/3.98      | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_83204,c_4397]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_83208,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_83204,c_1514]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84329,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0 | sP2_iProver_split = iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_83209,c_37,c_1018,c_1877,c_1895,c_2636,c_83208]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6116,plain,
% 27.30/3.98      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 27.30/3.98      | sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(X0,sK2) != iProver_top
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6084,c_1493]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84507,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 27.30/3.98      | sP2_iProver_split != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_84449,c_6116]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84533,plain,
% 27.30/3.98      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top | sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_84509,c_84329,c_84507]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84534,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0 | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 27.30/3.98      inference(renaming,[status(thm)],[c_84533]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84543,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0 | v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_6098,c_84534]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84542,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_8289,c_84534]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84562,plain,
% 27.30/3.98      ( sK3 = k1_xboole_0 ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_84543,c_2636,c_84318,c_84542]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84981,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 27.30/3.98      inference(demodulation,[status(thm)],[c_84562,c_1505]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_0,plain,
% 27.30/3.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.30/3.98      inference(cnf_transformation,[],[f74]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_84986,plain,
% 27.30/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 27.30/3.98      inference(demodulation,[status(thm)],[c_84981,c_0]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1,plain,
% 27.30/3.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.30/3.98      inference(cnf_transformation,[],[f75]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2495,plain,
% 27.30/3.98      ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
% 27.30/3.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_1,c_1512]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_85100,plain,
% 27.30/3.98      ( k2_relset_1(k1_xboole_0,X0,sK4) = k2_relat_1(sK4) ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_84986,c_2495]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_91539,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_85100,c_1514]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_91576,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.30/3.98      inference(light_normalisation,[status(thm)],[c_91539,c_1]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2,plain,
% 27.30/3.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 27.30/3.98      | k1_xboole_0 = X1
% 27.30/3.98      | k1_xboole_0 = X0 ),
% 27.30/3.98      inference(cnf_transformation,[],[f41]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_103,plain,
% 27.30/3.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 27.30/3.98      | k1_xboole_0 = k1_xboole_0 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_2]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_104,plain,
% 27.30/3.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_1]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_978,plain,
% 27.30/3.98      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 27.30/3.98      theory(equality) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_990,plain,
% 27.30/3.98      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 27.30/3.98      | k1_xboole_0 != k1_xboole_0 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_978]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1791,plain,
% 27.30/3.98      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 27.30/3.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_7]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1792,plain,
% 27.30/3.98      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1797,plain,
% 27.30/3.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 27.30/3.98      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_9]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_17,plain,
% 27.30/3.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 27.30/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(cnf_transformation,[],[f60]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_341,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.30/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
% 27.30/3.98      | ~ v1_funct_1(X2)
% 27.30/3.98      | ~ v1_relat_1(X2)
% 27.30/3.98      | X3 != X1
% 27.30/3.98      | k2_relat_1(X2) != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_342,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 27.30/3.98      | ~ v1_funct_1(X0)
% 27.30/3.98      | ~ v1_relat_1(X0) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_341]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_468,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.30/3.98      | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 27.30/3.98      | ~ v1_relat_1(X0)
% 27.30/3.98      | sK4 != X0 ),
% 27.30/3.98      inference(resolution_lifted,[status(thm)],[c_342,c_30]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_469,plain,
% 27.30/3.98      ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0))
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 27.30/3.98      | ~ v1_relat_1(sK4) ),
% 27.30/3.98      inference(unflattening,[status(thm)],[c_468]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1500,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1826,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 27.30/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.30/3.98      | v1_relat_1(sK4) != iProver_top ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_0,c_1500]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2417,plain,
% 27.30/3.98      ( k1_zfmisc_1(sK3) = k1_zfmisc_1(X0) | sK3 != X0 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_978]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2419,plain,
% 27.30/3.98      ( k1_zfmisc_1(sK3) = k1_zfmisc_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_2417]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_975,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2316,plain,
% 27.30/3.98      ( X0 != X1
% 27.30/3.98      | X0 = k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k2_relset_1(sK2,sK3,sK4) != X1 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_975]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3525,plain,
% 27.30/3.98      ( X0 = k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | X0 != k2_relat_1(sK4)
% 27.30/3.98      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_2316]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3840,plain,
% 27.30/3.98      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 27.30/3.98      | k2_relat_1(sK4) = k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k2_relat_1(sK4) != k2_relat_1(sK4) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_3525]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_974,plain,( X0 = X0 ),theory(equality) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_3841,plain,
% 27.30/3.98      ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_974]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_977,plain,
% 27.30/3.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.30/3.98      theory(equality) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1819,plain,
% 27.30/3.98      ( m1_subset_1(X0,X1)
% 27.30/3.98      | ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 27.30/3.98      | X0 != k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | X1 != k1_zfmisc_1(sK3) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_977]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1975,plain,
% 27.30/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.30/3.98      | ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 27.30/3.98      | X0 != k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK3) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_1819]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6839,plain,
% 27.30/3.98      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 27.30/3.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0))
% 27.30/3.98      | k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_1975]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6840,plain,
% 27.30/3.98      ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 27.30/3.98      | m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 27.30/3.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
% 27.30/3.98      inference(predicate_to_equality,[status(thm)],[c_6839]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6842,plain,
% 27.30/3.98      ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
% 27.30/3.98      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3)
% 27.30/3.98      | m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 27.30/3.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_6840]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_1973,plain,
% 27.30/3.98      ( X0 != X1 | X0 = k1_zfmisc_1(sK3) | k1_zfmisc_1(sK3) != X1 ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_975]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_2416,plain,
% 27.30/3.98      ( X0 != k1_zfmisc_1(X1)
% 27.30/3.98      | X0 = k1_zfmisc_1(sK3)
% 27.30/3.98      | k1_zfmisc_1(sK3) != k1_zfmisc_1(X1) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_1973]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6943,plain,
% 27.30/3.98      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 27.30/3.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3)
% 27.30/3.98      | k1_zfmisc_1(sK3) != k1_zfmisc_1(X1) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_6944,plain,
% 27.30/3.98      ( k1_zfmisc_1(sK3) != k1_zfmisc_1(k1_xboole_0)
% 27.30/3.98      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
% 27.30/3.98      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 27.30/3.98      inference(instantiation,[status(thm)],[c_6943]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_92637,plain,
% 27.30/3.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
% 27.30/3.98      inference(global_propositional_subsumption,
% 27.30/3.98                [status(thm)],
% 27.30/3.98                [c_91576,c_28,c_37,c_103,c_104,c_990,c_1792,c_1797,c_1826,
% 27.30/3.98                 c_1877,c_1895,c_2419,c_2636,c_3840,c_3841,c_6842,c_6944,
% 27.30/3.98                 c_84318,c_84542]) ).
% 27.30/3.98  
% 27.30/3.98  cnf(c_92656,plain,
% 27.30/3.98      ( $false ),
% 27.30/3.98      inference(superposition,[status(thm)],[c_92637,c_2636]) ).
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.30/3.98  
% 27.30/3.98  ------                               Statistics
% 27.30/3.98  
% 27.30/3.98  ------ General
% 27.30/3.98  
% 27.30/3.98  abstr_ref_over_cycles:                  0
% 27.30/3.98  abstr_ref_under_cycles:                 0
% 27.30/3.98  gc_basic_clause_elim:                   0
% 27.30/3.98  forced_gc_time:                         0
% 27.30/3.98  parsing_time:                           0.01
% 27.30/3.98  unif_index_cands_time:                  0.
% 27.30/3.98  unif_index_add_time:                    0.
% 27.30/3.98  orderings_time:                         0.
% 27.30/3.98  out_proof_time:                         0.021
% 27.30/3.98  total_time:                             3.012
% 27.30/3.98  num_of_symbols:                         55
% 27.30/3.98  num_of_terms:                           58111
% 27.30/3.98  
% 27.30/3.98  ------ Preprocessing
% 27.30/3.98  
% 27.30/3.98  num_of_splits:                          6
% 27.30/3.98  num_of_split_atoms:                     3
% 27.30/3.98  num_of_reused_defs:                     3
% 27.30/3.98  num_eq_ax_congr_red:                    14
% 27.30/3.98  num_of_sem_filtered_clauses:            1
% 27.30/3.98  num_of_subtypes:                        0
% 27.30/3.98  monotx_restored_types:                  0
% 27.30/3.98  sat_num_of_epr_types:                   0
% 27.30/3.98  sat_num_of_non_cyclic_types:            0
% 27.30/3.98  sat_guarded_non_collapsed_types:        0
% 27.30/3.98  num_pure_diseq_elim:                    0
% 27.30/3.98  simp_replaced_by:                       0
% 27.30/3.98  res_preprocessed:                       155
% 27.30/3.98  prep_upred:                             0
% 27.30/3.98  prep_unflattend:                        28
% 27.30/3.98  smt_new_axioms:                         0
% 27.30/3.98  pred_elim_cands:                        3
% 27.30/3.98  pred_elim:                              4
% 27.30/3.98  pred_elim_cl:                           0
% 27.30/3.98  pred_elim_cycles:                       6
% 27.30/3.98  merged_defs:                            0
% 27.30/3.98  merged_defs_ncl:                        0
% 27.30/3.98  bin_hyper_res:                          0
% 27.30/3.98  prep_cycles:                            4
% 27.30/3.98  pred_elim_time:                         0.01
% 27.30/3.98  splitting_time:                         0.
% 27.30/3.98  sem_filter_time:                        0.
% 27.30/3.98  monotx_time:                            0.
% 27.30/3.98  subtype_inf_time:                       0.
% 27.30/3.98  
% 27.30/3.98  ------ Problem properties
% 27.30/3.98  
% 27.30/3.98  clauses:                                36
% 27.30/3.98  conjectures:                            2
% 27.30/3.98  epr:                                    1
% 27.30/3.98  horn:                                   23
% 27.30/3.98  ground:                                 9
% 27.30/3.98  unary:                                  6
% 27.30/3.98  binary:                                 4
% 27.30/3.98  lits:                                   97
% 27.30/3.98  lits_eq:                                24
% 27.30/3.98  fd_pure:                                0
% 27.30/3.98  fd_pseudo:                              0
% 27.30/3.98  fd_cond:                                4
% 27.30/3.98  fd_pseudo_cond:                         0
% 27.30/3.98  ac_symbols:                             0
% 27.30/3.98  
% 27.30/3.98  ------ Propositional Solver
% 27.30/3.98  
% 27.30/3.98  prop_solver_calls:                      44
% 27.30/3.98  prop_fast_solver_calls:                 4688
% 27.30/3.98  smt_solver_calls:                       0
% 27.30/3.98  smt_fast_solver_calls:                  0
% 27.30/3.98  prop_num_of_clauses:                    21427
% 27.30/3.98  prop_preprocess_simplified:             41526
% 27.30/3.98  prop_fo_subsumed:                       193
% 27.30/3.98  prop_solver_time:                       0.
% 27.30/3.98  smt_solver_time:                        0.
% 27.30/3.98  smt_fast_solver_time:                   0.
% 27.30/3.98  prop_fast_solver_time:                  0.
% 27.30/3.98  prop_unsat_core_time:                   0.
% 27.30/3.98  
% 27.30/3.98  ------ QBF
% 27.30/3.98  
% 27.30/3.98  qbf_q_res:                              0
% 27.30/3.98  qbf_num_tautologies:                    0
% 27.30/3.98  qbf_prep_cycles:                        0
% 27.30/3.98  
% 27.30/3.98  ------ BMC1
% 27.30/3.98  
% 27.30/3.98  bmc1_current_bound:                     -1
% 27.30/3.98  bmc1_last_solved_bound:                 -1
% 27.30/3.98  bmc1_unsat_core_size:                   -1
% 27.30/3.98  bmc1_unsat_core_parents_size:           -1
% 27.30/3.98  bmc1_merge_next_fun:                    0
% 27.30/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.30/3.98  
% 27.30/3.98  ------ Instantiation
% 27.30/3.98  
% 27.30/3.98  inst_num_of_clauses:                    2407
% 27.30/3.98  inst_num_in_passive:                    452
% 27.30/3.98  inst_num_in_active:                     3854
% 27.30/3.98  inst_num_in_unprocessed:                770
% 27.30/3.98  inst_num_of_loops:                      4199
% 27.30/3.98  inst_num_of_learning_restarts:          1
% 27.30/3.98  inst_num_moves_active_passive:          334
% 27.30/3.98  inst_lit_activity:                      0
% 27.30/3.98  inst_lit_activity_moves:                0
% 27.30/3.98  inst_num_tautologies:                   0
% 27.30/3.98  inst_num_prop_implied:                  0
% 27.30/3.98  inst_num_existing_simplified:           0
% 27.30/3.98  inst_num_eq_res_simplified:             0
% 27.30/3.98  inst_num_child_elim:                    0
% 27.30/3.98  inst_num_of_dismatching_blockings:      1809
% 27.30/3.98  inst_num_of_non_proper_insts:           5803
% 27.30/3.98  inst_num_of_duplicates:                 0
% 27.30/3.98  inst_inst_num_from_inst_to_res:         0
% 27.30/3.98  inst_dismatching_checking_time:         0.
% 27.30/3.98  
% 27.30/3.98  ------ Resolution
% 27.30/3.98  
% 27.30/3.98  res_num_of_clauses:                     47
% 27.30/3.98  res_num_in_passive:                     47
% 27.30/3.98  res_num_in_active:                      0
% 27.30/3.98  res_num_of_loops:                       159
% 27.30/3.98  res_forward_subset_subsumed:            244
% 27.30/3.98  res_backward_subset_subsumed:           6
% 27.30/3.98  res_forward_subsumed:                   0
% 27.30/3.98  res_backward_subsumed:                  0
% 27.30/3.98  res_forward_subsumption_resolution:     0
% 27.30/3.98  res_backward_subsumption_resolution:    0
% 27.30/3.98  res_clause_to_clause_subsumption:       34654
% 27.30/3.98  res_orphan_elimination:                 0
% 27.30/3.98  res_tautology_del:                      531
% 27.30/3.98  res_num_eq_res_simplified:              0
% 27.30/3.98  res_num_sel_changes:                    0
% 27.30/3.98  res_moves_from_active_to_pass:          0
% 27.30/3.98  
% 27.30/3.98  ------ Superposition
% 27.30/3.98  
% 27.30/3.98  sup_time_total:                         0.
% 27.30/3.98  sup_time_generating:                    0.
% 27.30/3.98  sup_time_sim_full:                      0.
% 27.30/3.98  sup_time_sim_immed:                     0.
% 27.30/3.98  
% 27.30/3.98  sup_num_of_clauses:                     2928
% 27.30/3.98  sup_num_in_active:                      265
% 27.30/3.98  sup_num_in_passive:                     2663
% 27.30/3.98  sup_num_of_loops:                       838
% 27.30/3.98  sup_fw_superposition:                   2265
% 27.30/3.98  sup_bw_superposition:                   3093
% 27.30/3.98  sup_immediate_simplified:               2527
% 27.30/3.98  sup_given_eliminated:                   0
% 27.30/3.98  comparisons_done:                       0
% 27.30/3.98  comparisons_avoided:                    3894
% 27.30/3.98  
% 27.30/3.98  ------ Simplifications
% 27.30/3.98  
% 27.30/3.98  
% 27.30/3.98  sim_fw_subset_subsumed:                 213
% 27.30/3.98  sim_bw_subset_subsumed:                 287
% 27.30/3.98  sim_fw_subsumed:                        190
% 27.30/3.98  sim_bw_subsumed:                        220
% 27.30/3.98  sim_fw_subsumption_res:                 4
% 27.30/3.98  sim_bw_subsumption_res:                 0
% 27.30/3.98  sim_tautology_del:                      1
% 27.30/3.98  sim_eq_tautology_del:                   968
% 27.30/3.98  sim_eq_res_simp:                        2
% 27.30/3.98  sim_fw_demodulated:                     819
% 27.30/3.98  sim_bw_demodulated:                     1489
% 27.30/3.98  sim_light_normalised:                   237
% 27.30/3.98  sim_joinable_taut:                      0
% 27.30/3.98  sim_joinable_simp:                      0
% 27.30/3.98  sim_ac_normalised:                      0
% 27.30/3.98  sim_smt_subsumption:                    0
% 27.30/3.98  
%------------------------------------------------------------------------------
