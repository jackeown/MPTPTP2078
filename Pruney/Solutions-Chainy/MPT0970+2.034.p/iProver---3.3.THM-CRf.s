%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:52 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  180 (2646 expanded)
%              Number of clauses        :  111 ( 947 expanded)
%              Number of leaves         :   22 ( 612 expanded)
%              Depth                    :   27
%              Number of atoms          :  607 (12034 expanded)
%              Number of equality atoms :  278 (3508 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK8(X3)) = X3
        & r2_hidden(sK8(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK5,sK6,sK7) != sK6
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK7,X4) = X3
              & r2_hidden(X4,sK5) )
          | ~ r2_hidden(X3,sK6) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    & ! [X3] :
        ( ( k1_funct_1(sK7,sK8(X3)) = X3
          & r2_hidden(sK8(X3),sK5) )
        | ~ r2_hidden(X3,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f46,f45])).

fof(f78,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X3] :
      ( r2_hidden(sK8(X3),sK5)
      | ~ r2_hidden(X3,sK6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X3] :
      ( k1_funct_1(sK7,sK8(X3)) = X3
      | ~ r2_hidden(X3,sK6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f83,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1720,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1714,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_4133,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_1714])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_458,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_459,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_864,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_459])).

cnf(c_865,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_1141,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1983,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1985,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_2038,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_1983,c_1985])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_834,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_459])).

cnf(c_835,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_1122,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_835])).

cnf(c_1687,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_1123,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_835])).

cnf(c_1180,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_1181,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_849,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_459])).

cnf(c_850,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK1(X0,X1,sK7),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_1119,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_850])).

cnf(c_1984,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_1988,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_2848,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1687,c_1180,c_1181,c_1983,c_1988])).

cnf(c_2849,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_2848])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_390,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1713,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_2141,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1713])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1718,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2162,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_1718])).

cnf(c_2857,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_2162])).

cnf(c_4351,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_2857])).

cnf(c_4796,plain,
    ( k2_relat_1(sK7) = k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4351])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_440,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_441,plain,
    ( k2_relset_1(X0,X1,sK7) = k2_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1982,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_441])).

cnf(c_2009,plain,
    ( k2_relat_1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_1982,c_28])).

cnf(c_1142,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1998,plain,
    ( k2_relset_1(sK5,sK6,sK7) != X0
    | k2_relset_1(sK5,sK6,sK7) = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2087,plain,
    ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(sK7)
    | k2_relset_1(sK5,sK6,sK7) = sK6
    | sK6 != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_2049,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2199,plain,
    ( k2_relat_1(sK7) != X0
    | sK6 != X0
    | sK6 = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_2200,plain,
    ( k2_relat_1(sK7) != k1_xboole_0
    | sK6 = k2_relat_1(sK7)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2199])).

cnf(c_4783,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_4351])).

cnf(c_5551,plain,
    ( k2_relat_1(sK7) = sK6
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4783])).

cnf(c_5553,plain,
    ( k2_relat_1(sK7) = sK6
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5551])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK8(X0),sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3406,plain,
    ( ~ r2_hidden(sK0(X0,sK6),sK6)
    | r2_hidden(sK8(sK0(X0,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5968,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
    | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_5969,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top
    | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5968])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_405,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_929,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != sK7
    | sK6 != X1
    | sK5 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_405])).

cnf(c_930,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_1002,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_930])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_449,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_450,plain,
    ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1992,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_450])).

cnf(c_2145,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1002,c_1992])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,sK8(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1716,plain,
    ( k1_funct_1(sK7,sK8(X0)) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5541,plain,
    ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),X0))) = sK0(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = X0
    | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_1716])).

cnf(c_5707,plain,
    ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k2_relat_1(sK7),sK6)
    | k2_relat_1(sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_5541,c_1716])).

cnf(c_5829,plain,
    ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k2_relat_1(sK7),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5707,c_2009])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_640,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_641,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_459,c_641])).

cnf(c_1136,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ sP9_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP9_iProver_split])],[c_724])).

cnf(c_1708,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | sP9_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_1137,plain,
    ( sP9_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_724])).

cnf(c_1213,plain,
    ( sP9_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_1214,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | sP9_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_2770,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1708,c_1213,c_1214,c_1983,c_1988])).

cnf(c_2771,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2770])).

cnf(c_5832,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5829,c_2771])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2043,plain,
    ( ~ r2_hidden(sK0(X0,sK6),X0)
    | ~ r2_hidden(sK0(X0,sK6),sK6)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2238,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
    | sK6 = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2043])).

cnf(c_2239,plain,
    ( sK6 = k2_relat_1(sK7)
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_6071,plain,
    ( r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5832,c_28,c_1982,c_2009,c_2087,c_2239,c_5553])).

cnf(c_6076,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_6071])).

cnf(c_6632,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4796,c_28,c_1982,c_2009,c_2087,c_2200,c_5553,c_5969,c_6076])).

cnf(c_2148,plain,
    ( k9_relat_1(sK7,sK5) = k2_relat_1(sK7)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2145,c_2038])).

cnf(c_4337,plain,
    ( k9_relat_1(sK7,X0) = X1
    | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),X1) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_2857])).

cnf(c_5627,plain,
    ( k1_funct_1(sK7,sK8(sK0(k9_relat_1(sK7,X0),X1))) = sK0(k9_relat_1(sK7,X0),X1)
    | k9_relat_1(sK7,X0) = X1
    | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4337,c_1716])).

cnf(c_5854,plain,
    ( k1_funct_1(sK7,sK8(sK0(k9_relat_1(sK7,X0),sK6))) = sK0(k9_relat_1(sK7,X0),sK6)
    | k9_relat_1(sK7,X0) = sK6 ),
    inference(superposition,[status(thm)],[c_5627,c_1716])).

cnf(c_6037,plain,
    ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k9_relat_1(sK7,sK5),sK6)
    | k9_relat_1(sK7,sK5) = sK6
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2148,c_5854])).

cnf(c_6059,plain,
    ( k9_relat_1(sK7,sK5) = sK6
    | sK0(k9_relat_1(sK7,sK5),sK6) = sK0(k2_relat_1(sK7),sK6)
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6037,c_5829])).

cnf(c_6330,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6059,c_2009,c_5553,c_5969,c_6076])).

cnf(c_6636,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6632,c_6330])).

cnf(c_6638,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6636,c_1714])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:56:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.99  
% 3.51/0.99  ------  iProver source info
% 3.51/0.99  
% 3.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.99  git: non_committed_changes: false
% 3.51/0.99  git: last_make_outside_of_git: false
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     num_symb
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       true
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  ------ Parsing...
% 3.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... gs_s  sp: 20 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.99  ------ Proving...
% 3.51/0.99  ------ Problem Properties 
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  clauses                                 46
% 3.51/0.99  conjectures                             3
% 3.51/0.99  EPR                                     11
% 3.51/0.99  Horn                                    31
% 3.51/0.99  unary                                   2
% 3.51/0.99  binary                                  28
% 3.51/0.99  lits                                    113
% 3.51/0.99  lits eq                                 36
% 3.51/0.99  fd_pure                                 0
% 3.51/0.99  fd_pseudo                               0
% 3.51/0.99  fd_cond                                 3
% 3.51/0.99  fd_pseudo_cond                          2
% 3.51/0.99  AC symbols                              0
% 3.51/0.99  
% 3.51/0.99  ------ Schedule dynamic 5 is on 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  Current options:
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     none
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       false
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ Proving...
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS status Theorem for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99   Resolution empty clause
% 3.51/0.99  
% 3.51/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  fof(f1,axiom,(
% 3.51/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f15,plain,(
% 3.51/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.51/0.99    inference(ennf_transformation,[],[f1])).
% 3.51/0.99  
% 3.51/0.99  fof(f29,plain,(
% 3.51/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.51/0.99    inference(nnf_transformation,[],[f15])).
% 3.51/0.99  
% 3.51/0.99  fof(f30,plain,(
% 3.51/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f31,plain,(
% 3.51/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.51/0.99  
% 3.51/0.99  fof(f48,plain,(
% 3.51/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f31])).
% 3.51/0.99  
% 3.51/0.99  fof(f2,axiom,(
% 3.51/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f50,plain,(
% 3.51/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f2])).
% 3.51/0.99  
% 3.51/0.99  fof(f8,axiom,(
% 3.51/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f21,plain,(
% 3.51/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.51/0.99    inference(ennf_transformation,[],[f8])).
% 3.51/0.99  
% 3.51/0.99  fof(f66,plain,(
% 3.51/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f21])).
% 3.51/0.99  
% 3.51/0.99  fof(f6,axiom,(
% 3.51/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f18,plain,(
% 3.51/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f6])).
% 3.51/0.99  
% 3.51/0.99  fof(f59,plain,(
% 3.51/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f18])).
% 3.51/0.99  
% 3.51/0.99  fof(f9,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f22,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f9])).
% 3.51/0.99  
% 3.51/0.99  fof(f67,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f22])).
% 3.51/0.99  
% 3.51/0.99  fof(f13,conjecture,(
% 3.51/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f14,negated_conjecture,(
% 3.51/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.51/0.99    inference(negated_conjecture,[],[f13])).
% 3.51/0.99  
% 3.51/0.99  fof(f27,plain,(
% 3.51/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.51/0.99    inference(ennf_transformation,[],[f14])).
% 3.51/0.99  
% 3.51/0.99  fof(f28,plain,(
% 3.51/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.51/0.99    inference(flattening,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f46,plain,(
% 3.51/0.99    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK8(X3)) = X3 & r2_hidden(sK8(X3),X0)))) )),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f45,plain,(
% 3.51/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK5,sK6,sK7) != sK6 & ! [X3] : (? [X4] : (k1_funct_1(sK7,X4) = X3 & r2_hidden(X4,sK5)) | ~r2_hidden(X3,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f47,plain,(
% 3.51/0.99    k2_relset_1(sK5,sK6,sK7) != sK6 & ! [X3] : ((k1_funct_1(sK7,sK8(X3)) = X3 & r2_hidden(sK8(X3),sK5)) | ~r2_hidden(X3,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f46,f45])).
% 3.51/0.99  
% 3.51/0.99  fof(f78,plain,(
% 3.51/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f5,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f17,plain,(
% 3.51/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.51/0.99    inference(ennf_transformation,[],[f5])).
% 3.51/0.99  
% 3.51/0.99  fof(f34,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.51/0.99    inference(nnf_transformation,[],[f17])).
% 3.51/0.99  
% 3.51/0.99  fof(f35,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.51/0.99    inference(rectify,[],[f34])).
% 3.51/0.99  
% 3.51/0.99  fof(f36,plain,(
% 3.51/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f37,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.51/0.99  
% 3.51/0.99  fof(f56,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f37])).
% 3.51/0.99  
% 3.51/0.99  fof(f57,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f37])).
% 3.51/0.99  
% 3.51/0.99  fof(f4,axiom,(
% 3.51/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f16,plain,(
% 3.51/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f4])).
% 3.51/0.99  
% 3.51/0.99  fof(f54,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f16])).
% 3.51/0.99  
% 3.51/0.99  fof(f3,axiom,(
% 3.51/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f32,plain,(
% 3.51/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.51/0.99    inference(nnf_transformation,[],[f3])).
% 3.51/0.99  
% 3.51/0.99  fof(f33,plain,(
% 3.51/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.51/0.99    inference(flattening,[],[f32])).
% 3.51/0.99  
% 3.51/0.99  fof(f52,plain,(
% 3.51/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f33])).
% 3.51/0.99  
% 3.51/0.99  fof(f81,plain,(
% 3.51/0.99    k2_relset_1(sK5,sK6,sK7) != sK6),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f11,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f24,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f11])).
% 3.51/0.99  
% 3.51/0.99  fof(f69,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f24])).
% 3.51/1.00  
% 3.51/1.00  fof(f79,plain,(
% 3.51/1.00    ( ! [X3] : (r2_hidden(sK8(X3),sK5) | ~r2_hidden(X3,sK6)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f47])).
% 3.51/1.00  
% 3.51/1.00  fof(f77,plain,(
% 3.51/1.00    v1_funct_2(sK7,sK5,sK6)),
% 3.51/1.00    inference(cnf_transformation,[],[f47])).
% 3.51/1.00  
% 3.51/1.00  fof(f12,axiom,(
% 3.51/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f25,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/1.00    inference(ennf_transformation,[],[f12])).
% 3.51/1.00  
% 3.51/1.00  fof(f26,plain,(
% 3.51/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/1.00    inference(flattening,[],[f25])).
% 3.51/1.00  
% 3.51/1.00  fof(f44,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/1.00    inference(nnf_transformation,[],[f26])).
% 3.51/1.00  
% 3.51/1.00  fof(f70,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f44])).
% 3.51/1.00  
% 3.51/1.00  fof(f10,axiom,(
% 3.51/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f23,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/1.00    inference(ennf_transformation,[],[f10])).
% 3.51/1.00  
% 3.51/1.00  fof(f68,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f23])).
% 3.51/1.00  
% 3.51/1.00  fof(f80,plain,(
% 3.51/1.00    ( ! [X3] : (k1_funct_1(sK7,sK8(X3)) = X3 | ~r2_hidden(X3,sK6)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f47])).
% 3.51/1.00  
% 3.51/1.00  fof(f7,axiom,(
% 3.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f19,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f7])).
% 3.51/1.00  
% 3.51/1.00  fof(f20,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/1.00    inference(flattening,[],[f19])).
% 3.51/1.00  
% 3.51/1.00  fof(f38,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f20])).
% 3.51/1.00  
% 3.51/1.00  fof(f39,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/1.00    inference(rectify,[],[f38])).
% 3.51/1.00  
% 3.51/1.00  fof(f42,plain,(
% 3.51/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f41,plain,(
% 3.51/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f40,plain,(
% 3.51/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f43,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 3.51/1.00  
% 3.51/1.00  fof(f62,plain,(
% 3.51/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f82,plain,(
% 3.51/1.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/1.00    inference(equality_resolution,[],[f62])).
% 3.51/1.00  
% 3.51/1.00  fof(f83,plain,(
% 3.51/1.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/1.00    inference(equality_resolution,[],[f82])).
% 3.51/1.00  
% 3.51/1.00  fof(f76,plain,(
% 3.51/1.00    v1_funct_1(sK7)),
% 3.51/1.00    inference(cnf_transformation,[],[f47])).
% 3.51/1.00  
% 3.51/1.00  fof(f49,plain,(
% 3.51/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f31])).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1,plain,
% 3.51/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1720,plain,
% 3.51/1.00      ( X0 = X1
% 3.51/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.51/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2,plain,
% 3.51/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_18,plain,
% 3.51/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_378,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_379,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_378]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1714,plain,
% 3.51/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4133,plain,
% 3.51/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1720,c_1714]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11,plain,
% 3.51/1.00      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_19,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_31,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.51/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_458,plain,
% 3.51/1.00      ( v1_relat_1(X0)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X0 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_459,plain,
% 3.51/1.00      ( v1_relat_1(sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_458]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_864,plain,
% 3.51/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X0 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_459]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_865,plain,
% 3.51/1.00      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_864]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1141,plain,( X0 = X0 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1983,plain,
% 3.51/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1985,plain,
% 3.51/1.00      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_865]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2038,plain,
% 3.51/1.00      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_865,c_1983,c_1985]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.51/1.00      | ~ v1_relat_1(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_834,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_459]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_835,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_834]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1122,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7)
% 3.51/1.00      | ~ sP2_iProver_split ),
% 3.51/1.00      inference(splitting,
% 3.51/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.51/1.00                [c_835]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1687,plain,
% 3.51/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
% 3.51/1.00      | sP2_iProver_split != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1123,plain,
% 3.51/1.00      ( sP2_iProver_split | sP0_iProver_split ),
% 3.51/1.00      inference(splitting,
% 3.51/1.00                [splitting(split),new_symbols(definition,[])],
% 3.51/1.00                [c_835]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1180,plain,
% 3.51/1.00      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1181,plain,
% 3.51/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
% 3.51/1.00      | sP2_iProver_split != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.51/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.51/1.00      | ~ v1_relat_1(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_849,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.51/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_459]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_850,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.51/1.00      | r2_hidden(sK1(X0,X1,sK7),X1)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_849]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1119,plain,
% 3.51/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | ~ sP0_iProver_split ),
% 3.51/1.00      inference(splitting,
% 3.51/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.51/1.00                [c_850]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1984,plain,
% 3.51/1.00      ( ~ sP0_iProver_split
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1119]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1988,plain,
% 3.51/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sP0_iProver_split != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2848,plain,
% 3.51/1.00      ( r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top
% 3.51/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1687,c_1180,c_1181,c_1983,c_1988]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2849,plain,
% 3.51/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.51/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK7),X0),sK7) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_2848]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | ~ r2_hidden(X2,X0)
% 3.51/1.00      | r2_hidden(X2,X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_389,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,X1)
% 3.51/1.00      | r2_hidden(X0,X2)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X2)
% 3.51/1.00      | sK7 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_390,plain,
% 3.51/1.00      ( r2_hidden(X0,X1)
% 3.51/1.00      | ~ r2_hidden(X0,sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X1) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1713,plain,
% 3.51/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0)
% 3.51/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.51/1.00      | r2_hidden(X1,sK7) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2141,plain,
% 3.51/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.51/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_1713]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4,plain,
% 3.51/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1718,plain,
% 3.51/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.51/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2162,plain,
% 3.51/1.00      ( r2_hidden(X0,sK6) = iProver_top
% 3.51/1.00      | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2141,c_1718]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2857,plain,
% 3.51/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.51/1.00      | r2_hidden(X0,sK6) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2849,c_2162]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4351,plain,
% 3.51/1.00      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.51/1.00      | r2_hidden(X0,sK6) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2038,c_2857]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4796,plain,
% 3.51/1.00      ( k2_relat_1(sK7) = k1_xboole_0
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),sK6) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4133,c_4351]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_28,negated_conjecture,
% 3.51/1.00      ( k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 3.51/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_21,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_440,plain,
% 3.51/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_441,plain,
% 3.51/1.00      ( k2_relset_1(X0,X1,sK7) = k2_relat_1(sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_440]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1982,plain,
% 3.51/1.00      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_441]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2009,plain,
% 3.51/1.00      ( k2_relat_1(sK7) != sK6 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_1982,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1142,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1998,plain,
% 3.51/1.00      ( k2_relset_1(sK5,sK6,sK7) != X0
% 3.51/1.00      | k2_relset_1(sK5,sK6,sK7) = sK6
% 3.51/1.00      | sK6 != X0 ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1142]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2087,plain,
% 3.51/1.00      ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(sK7)
% 3.51/1.00      | k2_relset_1(sK5,sK6,sK7) = sK6
% 3.51/1.00      | sK6 != k2_relat_1(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1998]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2049,plain,
% 3.51/1.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1142]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2199,plain,
% 3.51/1.00      ( k2_relat_1(sK7) != X0 | sK6 != X0 | sK6 = k2_relat_1(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2049]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2200,plain,
% 3.51/1.00      ( k2_relat_1(sK7) != k1_xboole_0
% 3.51/1.00      | sK6 = k2_relat_1(sK7)
% 3.51/1.00      | sK6 != k1_xboole_0 ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2199]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4783,plain,
% 3.51/1.00      ( k2_relat_1(sK7) = X0
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) = iProver_top
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),X0),sK6) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1720,c_4351]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5551,plain,
% 3.51/1.00      ( k2_relat_1(sK7) = sK6
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top
% 3.51/1.00      | iProver_top != iProver_top ),
% 3.51/1.00      inference(equality_factoring,[status(thm)],[c_4783]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5553,plain,
% 3.51/1.00      ( k2_relat_1(sK7) = sK6
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
% 3.51/1.00      inference(equality_resolution_simp,[status(thm)],[c_5551]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_30,negated_conjecture,
% 3.51/1.00      ( ~ r2_hidden(X0,sK6) | r2_hidden(sK8(X0),sK5) ),
% 3.51/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3406,plain,
% 3.51/1.00      ( ~ r2_hidden(sK0(X0,sK6),sK6) | r2_hidden(sK8(sK0(X0,sK6)),sK5) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5968,plain,
% 3.51/1.00      ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
% 3.51/1.00      | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3406]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5969,plain,
% 3.51/1.00      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top
% 3.51/1.00      | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5968]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_32,negated_conjecture,
% 3.51/1.00      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.51/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_27,plain,
% 3.51/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.51/1.00      | k1_xboole_0 = X2 ),
% 3.51/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_404,plain,
% 3.51/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.51/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X0
% 3.51/1.00      | k1_xboole_0 = X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_405,plain,
% 3.51/1.00      ( ~ v1_funct_2(sK7,X0,X1)
% 3.51/1.00      | k1_relset_1(X0,X1,sK7) = X0
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | k1_xboole_0 = X1 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_929,plain,
% 3.51/1.00      ( k1_relset_1(X0,X1,sK7) = X0
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != sK7
% 3.51/1.00      | sK6 != X1
% 3.51/1.00      | sK5 != X0
% 3.51/1.00      | k1_xboole_0 = X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_405]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_930,plain,
% 3.51/1.00      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | k1_xboole_0 = sK6 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_929]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1002,plain,
% 3.51/1.00      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 3.51/1.00      inference(equality_resolution_simp,[status(thm)],[c_930]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_20,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_449,plain,
% 3.51/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.51/1.00      | sK7 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_450,plain,
% 3.51/1.00      ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1992,plain,
% 3.51/1.00      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_450]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2145,plain,
% 3.51/1.00      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_1002,c_1992]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_29,negated_conjecture,
% 3.51/1.00      ( ~ r2_hidden(X0,sK6) | k1_funct_1(sK7,sK8(X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1716,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(X0)) = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5541,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),X0))) = sK0(k2_relat_1(sK7),X0)
% 3.51/1.00      | k2_relat_1(sK7) = X0
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4783,c_1716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5707,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k2_relat_1(sK7),sK6)
% 3.51/1.00      | k2_relat_1(sK7) = sK6 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5541,c_1716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5829,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k2_relat_1(sK7),sK6) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5707,c_2009]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_15,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.51/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.51/1.00      | ~ v1_funct_1(X1)
% 3.51/1.00      | ~ v1_relat_1(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_33,negated_conjecture,
% 3.51/1.00      ( v1_funct_1(sK7) ),
% 3.51/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_640,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.51/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.51/1.00      | ~ v1_relat_1(X1)
% 3.51/1.00      | sK7 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_641,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.51/1.00      | ~ v1_relat_1(sK7) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_724,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.51/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.51/1.00      inference(resolution,[status(thm)],[c_459,c_641]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1136,plain,
% 3.51/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.51/1.00      | ~ sP9_iProver_split ),
% 3.51/1.00      inference(splitting,
% 3.51/1.00                [splitting(split),new_symbols(definition,[sP9_iProver_split])],
% 3.51/1.00                [c_724]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1708,plain,
% 3.51/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.51/1.00      | sP9_iProver_split != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1137,plain,
% 3.51/1.00      ( sP9_iProver_split | sP0_iProver_split ),
% 3.51/1.00      inference(splitting,
% 3.51/1.00                [splitting(split),new_symbols(definition,[])],
% 3.51/1.00                [c_724]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1213,plain,
% 3.51/1.00      ( sP9_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1214,plain,
% 3.51/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.51/1.00      | sP9_iProver_split != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2770,plain,
% 3.51/1.00      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.51/1.00      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1708,c_1213,c_1214,c_1983,c_1988]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2771,plain,
% 3.51/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.51/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_2770]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5832,plain,
% 3.51/1.00      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top
% 3.51/1.00      | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),k1_relat_1(sK7)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5829,c_2771]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_0,plain,
% 3.51/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | ~ r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2043,plain,
% 3.51/1.00      ( ~ r2_hidden(sK0(X0,sK6),X0) | ~ r2_hidden(sK0(X0,sK6),sK6) | sK6 = X0 ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2238,plain,
% 3.51/1.00      ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 3.51/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
% 3.51/1.00      | sK6 = k2_relat_1(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2043]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2239,plain,
% 3.51/1.00      ( sK6 = k2_relat_1(sK7)
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
% 3.51/1.00      | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6071,plain,
% 3.51/1.00      ( r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),k1_relat_1(sK7)) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5832,c_28,c_1982,c_2009,c_2087,c_2239,c_5553]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6076,plain,
% 3.51/1.00      ( sK6 = k1_xboole_0
% 3.51/1.00      | r2_hidden(sK8(sK0(k2_relat_1(sK7),sK6)),sK5) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2145,c_6071]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6632,plain,
% 3.51/1.00      ( r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),sK6) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4796,c_28,c_1982,c_2009,c_2087,c_2200,c_5553,c_5969,c_6076]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2148,plain,
% 3.51/1.00      ( k9_relat_1(sK7,sK5) = k2_relat_1(sK7) | sK6 = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2145,c_2038]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4337,plain,
% 3.51/1.00      ( k9_relat_1(sK7,X0) = X1
% 3.51/1.00      | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),X1) = iProver_top
% 3.51/1.00      | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),sK6) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1720,c_2857]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5627,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k9_relat_1(sK7,X0),X1))) = sK0(k9_relat_1(sK7,X0),X1)
% 3.51/1.00      | k9_relat_1(sK7,X0) = X1
% 3.51/1.00      | r2_hidden(sK0(k9_relat_1(sK7,X0),X1),X1) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4337,c_1716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5854,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k9_relat_1(sK7,X0),sK6))) = sK0(k9_relat_1(sK7,X0),sK6)
% 3.51/1.00      | k9_relat_1(sK7,X0) = sK6 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5627,c_1716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6037,plain,
% 3.51/1.00      ( k1_funct_1(sK7,sK8(sK0(k2_relat_1(sK7),sK6))) = sK0(k9_relat_1(sK7,sK5),sK6)
% 3.51/1.00      | k9_relat_1(sK7,sK5) = sK6
% 3.51/1.00      | sK6 = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2148,c_5854]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6059,plain,
% 3.51/1.00      ( k9_relat_1(sK7,sK5) = sK6
% 3.51/1.00      | sK0(k9_relat_1(sK7,sK5),sK6) = sK0(k2_relat_1(sK7),sK6)
% 3.51/1.00      | sK6 = k1_xboole_0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_6037,c_5829]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6330,plain,
% 3.51/1.00      ( sK6 = k1_xboole_0 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6059,c_2009,c_5553,c_5969,c_6076]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6636,plain,
% 3.51/1.00      ( r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_6632,c_6330]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6638,plain,
% 3.51/1.00      ( $false ),
% 3.51/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6636,c_1714]) ).
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  ------                               Statistics
% 3.51/1.00  
% 3.51/1.00  ------ General
% 3.51/1.00  
% 3.51/1.00  abstr_ref_over_cycles:                  0
% 3.51/1.00  abstr_ref_under_cycles:                 0
% 3.51/1.00  gc_basic_clause_elim:                   0
% 3.51/1.00  forced_gc_time:                         0
% 3.51/1.00  parsing_time:                           0.009
% 3.51/1.00  unif_index_cands_time:                  0.
% 3.51/1.00  unif_index_add_time:                    0.
% 3.51/1.00  orderings_time:                         0.
% 3.51/1.00  out_proof_time:                         0.009
% 3.51/1.00  total_time:                             0.213
% 3.51/1.00  num_of_symbols:                         67
% 3.51/1.00  num_of_terms:                           6717
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing
% 3.51/1.00  
% 3.51/1.00  num_of_splits:                          20
% 3.51/1.00  num_of_split_atoms:                     11
% 3.51/1.00  num_of_reused_defs:                     9
% 3.51/1.00  num_eq_ax_congr_red:                    38
% 3.51/1.00  num_of_sem_filtered_clauses:            1
% 3.51/1.00  num_of_subtypes:                        0
% 3.51/1.00  monotx_restored_types:                  0
% 3.51/1.00  sat_num_of_epr_types:                   0
% 3.51/1.00  sat_num_of_non_cyclic_types:            0
% 3.51/1.00  sat_guarded_non_collapsed_types:        0
% 3.51/1.00  num_pure_diseq_elim:                    0
% 3.51/1.00  simp_replaced_by:                       0
% 3.51/1.00  res_preprocessed:                       167
% 3.51/1.00  prep_upred:                             0
% 3.51/1.00  prep_unflattend:                        39
% 3.51/1.00  smt_new_axioms:                         0
% 3.51/1.00  pred_elim_cands:                        1
% 3.51/1.00  pred_elim:                              5
% 3.51/1.00  pred_elim_cl:                           8
% 3.51/1.00  pred_elim_cycles:                       7
% 3.51/1.00  merged_defs:                            0
% 3.51/1.00  merged_defs_ncl:                        0
% 3.51/1.00  bin_hyper_res:                          0
% 3.51/1.00  prep_cycles:                            4
% 3.51/1.00  pred_elim_time:                         0.013
% 3.51/1.00  splitting_time:                         0.
% 3.51/1.00  sem_filter_time:                        0.
% 3.51/1.00  monotx_time:                            0.
% 3.51/1.00  subtype_inf_time:                       0.
% 3.51/1.00  
% 3.51/1.00  ------ Problem properties
% 3.51/1.00  
% 3.51/1.00  clauses:                                46
% 3.51/1.00  conjectures:                            3
% 3.51/1.00  epr:                                    11
% 3.51/1.00  horn:                                   31
% 3.51/1.00  ground:                                 14
% 3.51/1.00  unary:                                  2
% 3.51/1.00  binary:                                 28
% 3.51/1.00  lits:                                   113
% 3.51/1.00  lits_eq:                                36
% 3.51/1.00  fd_pure:                                0
% 3.51/1.00  fd_pseudo:                              0
% 3.51/1.00  fd_cond:                                3
% 3.51/1.00  fd_pseudo_cond:                         2
% 3.51/1.00  ac_symbols:                             0
% 3.51/1.00  
% 3.51/1.00  ------ Propositional Solver
% 3.51/1.00  
% 3.51/1.00  prop_solver_calls:                      28
% 3.51/1.00  prop_fast_solver_calls:                 1283
% 3.51/1.00  smt_solver_calls:                       0
% 3.51/1.00  smt_fast_solver_calls:                  0
% 3.51/1.00  prop_num_of_clauses:                    2193
% 3.51/1.00  prop_preprocess_simplified:             7068
% 3.51/1.00  prop_fo_subsumed:                       35
% 3.51/1.00  prop_solver_time:                       0.
% 3.51/1.00  smt_solver_time:                        0.
% 3.51/1.00  smt_fast_solver_time:                   0.
% 3.51/1.00  prop_fast_solver_time:                  0.
% 3.51/1.00  prop_unsat_core_time:                   0.
% 3.51/1.00  
% 3.51/1.00  ------ QBF
% 3.51/1.00  
% 3.51/1.00  qbf_q_res:                              0
% 3.51/1.00  qbf_num_tautologies:                    0
% 3.51/1.00  qbf_prep_cycles:                        0
% 3.51/1.00  
% 3.51/1.00  ------ BMC1
% 3.51/1.00  
% 3.51/1.00  bmc1_current_bound:                     -1
% 3.51/1.00  bmc1_last_solved_bound:                 -1
% 3.51/1.00  bmc1_unsat_core_size:                   -1
% 3.51/1.00  bmc1_unsat_core_parents_size:           -1
% 3.51/1.00  bmc1_merge_next_fun:                    0
% 3.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation
% 3.51/1.00  
% 3.51/1.00  inst_num_of_clauses:                    637
% 3.51/1.00  inst_num_in_passive:                    275
% 3.51/1.00  inst_num_in_active:                     255
% 3.51/1.00  inst_num_in_unprocessed:                107
% 3.51/1.00  inst_num_of_loops:                      440
% 3.51/1.00  inst_num_of_learning_restarts:          0
% 3.51/1.00  inst_num_moves_active_passive:          181
% 3.51/1.00  inst_lit_activity:                      0
% 3.51/1.00  inst_lit_activity_moves:                0
% 3.51/1.00  inst_num_tautologies:                   0
% 3.51/1.00  inst_num_prop_implied:                  0
% 3.51/1.00  inst_num_existing_simplified:           0
% 3.51/1.00  inst_num_eq_res_simplified:             0
% 3.51/1.00  inst_num_child_elim:                    0
% 3.51/1.00  inst_num_of_dismatching_blockings:      148
% 3.51/1.00  inst_num_of_non_proper_insts:           456
% 3.51/1.00  inst_num_of_duplicates:                 0
% 3.51/1.00  inst_inst_num_from_inst_to_res:         0
% 3.51/1.00  inst_dismatching_checking_time:         0.
% 3.51/1.00  
% 3.51/1.00  ------ Resolution
% 3.51/1.00  
% 3.51/1.00  res_num_of_clauses:                     0
% 3.51/1.00  res_num_in_passive:                     0
% 3.51/1.00  res_num_in_active:                      0
% 3.51/1.00  res_num_of_loops:                       171
% 3.51/1.00  res_forward_subset_subsumed:            48
% 3.51/1.00  res_backward_subset_subsumed:           0
% 3.51/1.00  res_forward_subsumed:                   0
% 3.51/1.00  res_backward_subsumed:                  0
% 3.51/1.00  res_forward_subsumption_resolution:     0
% 3.51/1.00  res_backward_subsumption_resolution:    0
% 3.51/1.00  res_clause_to_clause_subsumption:       403
% 3.51/1.00  res_orphan_elimination:                 0
% 3.51/1.00  res_tautology_del:                      25
% 3.51/1.00  res_num_eq_res_simplified:              1
% 3.51/1.00  res_num_sel_changes:                    0
% 3.51/1.00  res_moves_from_active_to_pass:          0
% 3.51/1.00  
% 3.51/1.00  ------ Superposition
% 3.51/1.00  
% 3.51/1.00  sup_time_total:                         0.
% 3.51/1.00  sup_time_generating:                    0.
% 3.51/1.00  sup_time_sim_full:                      0.
% 3.51/1.00  sup_time_sim_immed:                     0.
% 3.51/1.00  
% 3.51/1.00  sup_num_of_clauses:                     164
% 3.51/1.00  sup_num_in_active:                      45
% 3.51/1.00  sup_num_in_passive:                     119
% 3.51/1.00  sup_num_of_loops:                       86
% 3.51/1.00  sup_fw_superposition:                   113
% 3.51/1.00  sup_bw_superposition:                   140
% 3.51/1.00  sup_immediate_simplified:               37
% 3.51/1.00  sup_given_eliminated:                   0
% 3.51/1.00  comparisons_done:                       0
% 3.51/1.00  comparisons_avoided:                    64
% 3.51/1.00  
% 3.51/1.00  ------ Simplifications
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  sim_fw_subset_subsumed:                 9
% 3.51/1.00  sim_bw_subset_subsumed:                 12
% 3.51/1.00  sim_fw_subsumed:                        14
% 3.51/1.00  sim_bw_subsumed:                        2
% 3.51/1.00  sim_fw_subsumption_res:                 1
% 3.51/1.00  sim_bw_subsumption_res:                 0
% 3.51/1.00  sim_tautology_del:                      4
% 3.51/1.00  sim_eq_tautology_del:                   36
% 3.51/1.00  sim_eq_res_simp:                        4
% 3.51/1.00  sim_fw_demodulated:                     10
% 3.51/1.00  sim_bw_demodulated:                     40
% 3.51/1.00  sim_light_normalised:                   15
% 3.51/1.00  sim_joinable_taut:                      0
% 3.51/1.00  sim_joinable_simp:                      0
% 3.51/1.00  sim_ac_normalised:                      0
% 3.51/1.00  sim_smt_subsumption:                    0
% 3.51/1.00  
%------------------------------------------------------------------------------
