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
% DateTime   : Thu Dec  3 12:00:34 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  226 (4448 expanded)
%              Number of clauses        :  145 (1794 expanded)
%              Number of leaves         :   23 ( 816 expanded)
%              Depth                    :   28
%              Number of atoms          :  674 (20346 expanded)
%              Number of equality atoms :  360 (6855 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f48])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f45])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_600,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_602,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_35])).

cnf(c_1491,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1495,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3761,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1491,c_1495])).

cnf(c_3936,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_602,c_3761])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_1489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_3701,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1489])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1494,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3173,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1491,c_1494])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1492,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3324,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3173,c_1492])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4587,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1495])).

cnf(c_13832,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_4587])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2468,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1500])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_272,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_273])).

cnf(c_1490,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_4451,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2468,c_1490])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1498,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4858,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4451,c_1498])).

cnf(c_14320,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13832,c_4858])).

cnf(c_14321,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14320])).

cnf(c_14331,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_14321])).

cnf(c_14382,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14331,c_4858])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_37])).

cnf(c_196,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_196])).

cnf(c_587,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_1484,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_14385,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14382,c_1484])).

cnf(c_2142,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2143,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2142])).

cnf(c_14492,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14385,c_2143,c_3324,c_3701,c_4858])).

cnf(c_14493,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_14492])).

cnf(c_14496,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3936,c_14493])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_14508,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14496,c_33])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1736,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_887,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2051,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2853,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_741,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_741])).

cnf(c_798,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_486,c_742])).

cnf(c_1482,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_3328,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_1482])).

cnf(c_3329,plain,
    ( ~ v1_xboole_0(sK3)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3328])).

cnf(c_4859,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4858])).

cnf(c_889,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4889,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_4891,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5625,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3700,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1489])).

cnf(c_7105,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_3700])).

cnf(c_7139,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3936,c_7105])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_890,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1798,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_1799,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_1801,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1487,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1616,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1487,c_6])).

cnf(c_888,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1747,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_1806,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_1807,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_2018,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_2019,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2131,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1616,c_33,c_108,c_109,c_1806,c_1807,c_2019])).

cnf(c_7528,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7139,c_108,c_109,c_112,c_1801,c_2131,c_4858])).

cnf(c_7529,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7528])).

cnf(c_7530,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7529])).

cnf(c_8401,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2868,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_6177,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_12253,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK4)
    | X0 != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6177])).

cnf(c_12255,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_12253])).

cnf(c_14639,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14508,c_0,c_1736,c_2051,c_2853,c_3329,c_4859,c_4891,c_5625,c_7530,c_8401,c_12255])).

cnf(c_14643,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_14639,c_14382])).

cnf(c_14714,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_14639,c_3761])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_574,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_1485,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_1609,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1485,c_7])).

cnf(c_14721,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14639,c_1609])).

cnf(c_14738,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14721])).

cnf(c_14724,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14639,c_1491])).

cnf(c_14727,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14724,c_7])).

cnf(c_14741,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14738,c_14727])).

cnf(c_14761,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14714,c_14741])).

cnf(c_14971,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14643,c_14761])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_196])).

cnf(c_558,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_1486,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1639,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1486,c_7])).

cnf(c_14720,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14639,c_1639])).

cnf(c_14743,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14720])).

cnf(c_14747,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14743,c_14727])).

cnf(c_14748,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14747,c_7])).

cnf(c_14973,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14971,c_14748])).

cnf(c_14975,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14973])).

cnf(c_14977,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14975,c_14727])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.92/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.03  
% 3.92/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/1.03  
% 3.92/1.03  ------  iProver source info
% 3.92/1.03  
% 3.92/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.92/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/1.03  git: non_committed_changes: false
% 3.92/1.03  git: last_make_outside_of_git: false
% 3.92/1.03  
% 3.92/1.03  ------ 
% 3.92/1.03  
% 3.92/1.03  ------ Input Options
% 3.92/1.03  
% 3.92/1.03  --out_options                           all
% 3.92/1.03  --tptp_safe_out                         true
% 3.92/1.03  --problem_path                          ""
% 3.92/1.03  --include_path                          ""
% 3.92/1.03  --clausifier                            res/vclausify_rel
% 3.92/1.03  --clausifier_options                    --mode clausify
% 3.92/1.03  --stdin                                 false
% 3.92/1.03  --stats_out                             all
% 3.92/1.03  
% 3.92/1.03  ------ General Options
% 3.92/1.03  
% 3.92/1.03  --fof                                   false
% 3.92/1.03  --time_out_real                         305.
% 3.92/1.03  --time_out_virtual                      -1.
% 3.92/1.03  --symbol_type_check                     false
% 3.92/1.03  --clausify_out                          false
% 3.92/1.03  --sig_cnt_out                           false
% 3.92/1.03  --trig_cnt_out                          false
% 3.92/1.03  --trig_cnt_out_tolerance                1.
% 3.92/1.03  --trig_cnt_out_sk_spl                   false
% 3.92/1.03  --abstr_cl_out                          false
% 3.92/1.03  
% 3.92/1.03  ------ Global Options
% 3.92/1.03  
% 3.92/1.03  --schedule                              default
% 3.92/1.03  --add_important_lit                     false
% 3.92/1.03  --prop_solver_per_cl                    1000
% 3.92/1.03  --min_unsat_core                        false
% 3.92/1.03  --soft_assumptions                      false
% 3.92/1.03  --soft_lemma_size                       3
% 3.92/1.03  --prop_impl_unit_size                   0
% 3.92/1.03  --prop_impl_unit                        []
% 3.92/1.03  --share_sel_clauses                     true
% 3.92/1.03  --reset_solvers                         false
% 3.92/1.03  --bc_imp_inh                            [conj_cone]
% 3.92/1.03  --conj_cone_tolerance                   3.
% 3.92/1.03  --extra_neg_conj                        none
% 3.92/1.03  --large_theory_mode                     true
% 3.92/1.03  --prolific_symb_bound                   200
% 3.92/1.03  --lt_threshold                          2000
% 3.92/1.03  --clause_weak_htbl                      true
% 3.92/1.03  --gc_record_bc_elim                     false
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing Options
% 3.92/1.03  
% 3.92/1.03  --preprocessing_flag                    true
% 3.92/1.03  --time_out_prep_mult                    0.1
% 3.92/1.03  --splitting_mode                        input
% 3.92/1.03  --splitting_grd                         true
% 3.92/1.03  --splitting_cvd                         false
% 3.92/1.03  --splitting_cvd_svl                     false
% 3.92/1.03  --splitting_nvd                         32
% 3.92/1.03  --sub_typing                            true
% 3.92/1.03  --prep_gs_sim                           true
% 3.92/1.03  --prep_unflatten                        true
% 3.92/1.03  --prep_res_sim                          true
% 3.92/1.03  --prep_upred                            true
% 3.92/1.03  --prep_sem_filter                       exhaustive
% 3.92/1.03  --prep_sem_filter_out                   false
% 3.92/1.03  --pred_elim                             true
% 3.92/1.03  --res_sim_input                         true
% 3.92/1.03  --eq_ax_congr_red                       true
% 3.92/1.03  --pure_diseq_elim                       true
% 3.92/1.03  --brand_transform                       false
% 3.92/1.03  --non_eq_to_eq                          false
% 3.92/1.03  --prep_def_merge                        true
% 3.92/1.03  --prep_def_merge_prop_impl              false
% 3.92/1.03  --prep_def_merge_mbd                    true
% 3.92/1.03  --prep_def_merge_tr_red                 false
% 3.92/1.03  --prep_def_merge_tr_cl                  false
% 3.92/1.03  --smt_preprocessing                     true
% 3.92/1.03  --smt_ac_axioms                         fast
% 3.92/1.03  --preprocessed_out                      false
% 3.92/1.03  --preprocessed_stats                    false
% 3.92/1.03  
% 3.92/1.03  ------ Abstraction refinement Options
% 3.92/1.03  
% 3.92/1.03  --abstr_ref                             []
% 3.92/1.03  --abstr_ref_prep                        false
% 3.92/1.03  --abstr_ref_until_sat                   false
% 3.92/1.03  --abstr_ref_sig_restrict                funpre
% 3.92/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.03  --abstr_ref_under                       []
% 3.92/1.03  
% 3.92/1.03  ------ SAT Options
% 3.92/1.03  
% 3.92/1.03  --sat_mode                              false
% 3.92/1.03  --sat_fm_restart_options                ""
% 3.92/1.03  --sat_gr_def                            false
% 3.92/1.03  --sat_epr_types                         true
% 3.92/1.03  --sat_non_cyclic_types                  false
% 3.92/1.03  --sat_finite_models                     false
% 3.92/1.03  --sat_fm_lemmas                         false
% 3.92/1.03  --sat_fm_prep                           false
% 3.92/1.03  --sat_fm_uc_incr                        true
% 3.92/1.03  --sat_out_model                         small
% 3.92/1.03  --sat_out_clauses                       false
% 3.92/1.03  
% 3.92/1.03  ------ QBF Options
% 3.92/1.03  
% 3.92/1.03  --qbf_mode                              false
% 3.92/1.03  --qbf_elim_univ                         false
% 3.92/1.03  --qbf_dom_inst                          none
% 3.92/1.03  --qbf_dom_pre_inst                      false
% 3.92/1.03  --qbf_sk_in                             false
% 3.92/1.03  --qbf_pred_elim                         true
% 3.92/1.03  --qbf_split                             512
% 3.92/1.03  
% 3.92/1.03  ------ BMC1 Options
% 3.92/1.03  
% 3.92/1.03  --bmc1_incremental                      false
% 3.92/1.03  --bmc1_axioms                           reachable_all
% 3.92/1.03  --bmc1_min_bound                        0
% 3.92/1.03  --bmc1_max_bound                        -1
% 3.92/1.03  --bmc1_max_bound_default                -1
% 3.92/1.03  --bmc1_symbol_reachability              true
% 3.92/1.03  --bmc1_property_lemmas                  false
% 3.92/1.03  --bmc1_k_induction                      false
% 3.92/1.03  --bmc1_non_equiv_states                 false
% 3.92/1.03  --bmc1_deadlock                         false
% 3.92/1.03  --bmc1_ucm                              false
% 3.92/1.03  --bmc1_add_unsat_core                   none
% 3.92/1.03  --bmc1_unsat_core_children              false
% 3.92/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.03  --bmc1_out_stat                         full
% 3.92/1.03  --bmc1_ground_init                      false
% 3.92/1.03  --bmc1_pre_inst_next_state              false
% 3.92/1.03  --bmc1_pre_inst_state                   false
% 3.92/1.03  --bmc1_pre_inst_reach_state             false
% 3.92/1.03  --bmc1_out_unsat_core                   false
% 3.92/1.03  --bmc1_aig_witness_out                  false
% 3.92/1.03  --bmc1_verbose                          false
% 3.92/1.03  --bmc1_dump_clauses_tptp                false
% 3.92/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.03  --bmc1_dump_file                        -
% 3.92/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.03  --bmc1_ucm_extend_mode                  1
% 3.92/1.03  --bmc1_ucm_init_mode                    2
% 3.92/1.03  --bmc1_ucm_cone_mode                    none
% 3.92/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.03  --bmc1_ucm_relax_model                  4
% 3.92/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.03  --bmc1_ucm_layered_model                none
% 3.92/1.03  --bmc1_ucm_max_lemma_size               10
% 3.92/1.03  
% 3.92/1.03  ------ AIG Options
% 3.92/1.03  
% 3.92/1.03  --aig_mode                              false
% 3.92/1.03  
% 3.92/1.03  ------ Instantiation Options
% 3.92/1.03  
% 3.92/1.03  --instantiation_flag                    true
% 3.92/1.03  --inst_sos_flag                         false
% 3.92/1.03  --inst_sos_phase                        true
% 3.92/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.03  --inst_lit_sel_side                     num_symb
% 3.92/1.03  --inst_solver_per_active                1400
% 3.92/1.03  --inst_solver_calls_frac                1.
% 3.92/1.03  --inst_passive_queue_type               priority_queues
% 3.92/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.03  --inst_passive_queues_freq              [25;2]
% 3.92/1.03  --inst_dismatching                      true
% 3.92/1.03  --inst_eager_unprocessed_to_passive     true
% 3.92/1.03  --inst_prop_sim_given                   true
% 3.92/1.03  --inst_prop_sim_new                     false
% 3.92/1.03  --inst_subs_new                         false
% 3.92/1.03  --inst_eq_res_simp                      false
% 3.92/1.03  --inst_subs_given                       false
% 3.92/1.03  --inst_orphan_elimination               true
% 3.92/1.03  --inst_learning_loop_flag               true
% 3.92/1.03  --inst_learning_start                   3000
% 3.92/1.03  --inst_learning_factor                  2
% 3.92/1.03  --inst_start_prop_sim_after_learn       3
% 3.92/1.03  --inst_sel_renew                        solver
% 3.92/1.03  --inst_lit_activity_flag                true
% 3.92/1.03  --inst_restr_to_given                   false
% 3.92/1.03  --inst_activity_threshold               500
% 3.92/1.03  --inst_out_proof                        true
% 3.92/1.03  
% 3.92/1.03  ------ Resolution Options
% 3.92/1.03  
% 3.92/1.03  --resolution_flag                       true
% 3.92/1.03  --res_lit_sel                           adaptive
% 3.92/1.03  --res_lit_sel_side                      none
% 3.92/1.03  --res_ordering                          kbo
% 3.92/1.03  --res_to_prop_solver                    active
% 3.92/1.03  --res_prop_simpl_new                    false
% 3.92/1.03  --res_prop_simpl_given                  true
% 3.92/1.03  --res_passive_queue_type                priority_queues
% 3.92/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.03  --res_passive_queues_freq               [15;5]
% 3.92/1.03  --res_forward_subs                      full
% 3.92/1.03  --res_backward_subs                     full
% 3.92/1.03  --res_forward_subs_resolution           true
% 3.92/1.03  --res_backward_subs_resolution          true
% 3.92/1.03  --res_orphan_elimination                true
% 3.92/1.03  --res_time_limit                        2.
% 3.92/1.03  --res_out_proof                         true
% 3.92/1.03  
% 3.92/1.03  ------ Superposition Options
% 3.92/1.03  
% 3.92/1.03  --superposition_flag                    true
% 3.92/1.03  --sup_passive_queue_type                priority_queues
% 3.92/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.92/1.03  --demod_completeness_check              fast
% 3.92/1.03  --demod_use_ground                      true
% 3.92/1.03  --sup_to_prop_solver                    passive
% 3.92/1.03  --sup_prop_simpl_new                    true
% 3.92/1.03  --sup_prop_simpl_given                  true
% 3.92/1.03  --sup_fun_splitting                     false
% 3.92/1.03  --sup_smt_interval                      50000
% 3.92/1.03  
% 3.92/1.03  ------ Superposition Simplification Setup
% 3.92/1.03  
% 3.92/1.03  --sup_indices_passive                   []
% 3.92/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_full_bw                           [BwDemod]
% 3.92/1.03  --sup_immed_triv                        [TrivRules]
% 3.92/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_immed_bw_main                     []
% 3.92/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.03  
% 3.92/1.03  ------ Combination Options
% 3.92/1.03  
% 3.92/1.03  --comb_res_mult                         3
% 3.92/1.03  --comb_sup_mult                         2
% 3.92/1.03  --comb_inst_mult                        10
% 3.92/1.03  
% 3.92/1.03  ------ Debug Options
% 3.92/1.03  
% 3.92/1.03  --dbg_backtrace                         false
% 3.92/1.03  --dbg_dump_prop_clauses                 false
% 3.92/1.03  --dbg_dump_prop_clauses_file            -
% 3.92/1.03  --dbg_out_stat                          false
% 3.92/1.03  ------ Parsing...
% 3.92/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/1.03  ------ Proving...
% 3.92/1.03  ------ Problem Properties 
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  clauses                                 32
% 3.92/1.03  conjectures                             3
% 3.92/1.03  EPR                                     8
% 3.92/1.03  Horn                                    29
% 3.92/1.03  unary                                   8
% 3.92/1.03  binary                                  11
% 3.92/1.03  lits                                    74
% 3.92/1.03  lits eq                                 35
% 3.92/1.03  fd_pure                                 0
% 3.92/1.03  fd_pseudo                               0
% 3.92/1.03  fd_cond                                 7
% 3.92/1.03  fd_pseudo_cond                          1
% 3.92/1.03  AC symbols                              0
% 3.92/1.03  
% 3.92/1.03  ------ Schedule dynamic 5 is on 
% 3.92/1.03  
% 3.92/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  ------ 
% 3.92/1.03  Current options:
% 3.92/1.03  ------ 
% 3.92/1.03  
% 3.92/1.03  ------ Input Options
% 3.92/1.03  
% 3.92/1.03  --out_options                           all
% 3.92/1.03  --tptp_safe_out                         true
% 3.92/1.03  --problem_path                          ""
% 3.92/1.03  --include_path                          ""
% 3.92/1.03  --clausifier                            res/vclausify_rel
% 3.92/1.03  --clausifier_options                    --mode clausify
% 3.92/1.03  --stdin                                 false
% 3.92/1.03  --stats_out                             all
% 3.92/1.03  
% 3.92/1.03  ------ General Options
% 3.92/1.03  
% 3.92/1.03  --fof                                   false
% 3.92/1.03  --time_out_real                         305.
% 3.92/1.03  --time_out_virtual                      -1.
% 3.92/1.03  --symbol_type_check                     false
% 3.92/1.03  --clausify_out                          false
% 3.92/1.03  --sig_cnt_out                           false
% 3.92/1.03  --trig_cnt_out                          false
% 3.92/1.03  --trig_cnt_out_tolerance                1.
% 3.92/1.03  --trig_cnt_out_sk_spl                   false
% 3.92/1.03  --abstr_cl_out                          false
% 3.92/1.03  
% 3.92/1.03  ------ Global Options
% 3.92/1.03  
% 3.92/1.03  --schedule                              default
% 3.92/1.03  --add_important_lit                     false
% 3.92/1.03  --prop_solver_per_cl                    1000
% 3.92/1.03  --min_unsat_core                        false
% 3.92/1.03  --soft_assumptions                      false
% 3.92/1.03  --soft_lemma_size                       3
% 3.92/1.03  --prop_impl_unit_size                   0
% 3.92/1.03  --prop_impl_unit                        []
% 3.92/1.03  --share_sel_clauses                     true
% 3.92/1.03  --reset_solvers                         false
% 3.92/1.03  --bc_imp_inh                            [conj_cone]
% 3.92/1.03  --conj_cone_tolerance                   3.
% 3.92/1.03  --extra_neg_conj                        none
% 3.92/1.03  --large_theory_mode                     true
% 3.92/1.03  --prolific_symb_bound                   200
% 3.92/1.03  --lt_threshold                          2000
% 3.92/1.03  --clause_weak_htbl                      true
% 3.92/1.03  --gc_record_bc_elim                     false
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing Options
% 3.92/1.03  
% 3.92/1.03  --preprocessing_flag                    true
% 3.92/1.03  --time_out_prep_mult                    0.1
% 3.92/1.03  --splitting_mode                        input
% 3.92/1.03  --splitting_grd                         true
% 3.92/1.03  --splitting_cvd                         false
% 3.92/1.03  --splitting_cvd_svl                     false
% 3.92/1.03  --splitting_nvd                         32
% 3.92/1.03  --sub_typing                            true
% 3.92/1.03  --prep_gs_sim                           true
% 3.92/1.03  --prep_unflatten                        true
% 3.92/1.03  --prep_res_sim                          true
% 3.92/1.03  --prep_upred                            true
% 3.92/1.03  --prep_sem_filter                       exhaustive
% 3.92/1.03  --prep_sem_filter_out                   false
% 3.92/1.03  --pred_elim                             true
% 3.92/1.03  --res_sim_input                         true
% 3.92/1.03  --eq_ax_congr_red                       true
% 3.92/1.03  --pure_diseq_elim                       true
% 3.92/1.03  --brand_transform                       false
% 3.92/1.03  --non_eq_to_eq                          false
% 3.92/1.03  --prep_def_merge                        true
% 3.92/1.03  --prep_def_merge_prop_impl              false
% 3.92/1.03  --prep_def_merge_mbd                    true
% 3.92/1.03  --prep_def_merge_tr_red                 false
% 3.92/1.03  --prep_def_merge_tr_cl                  false
% 3.92/1.03  --smt_preprocessing                     true
% 3.92/1.03  --smt_ac_axioms                         fast
% 3.92/1.03  --preprocessed_out                      false
% 3.92/1.03  --preprocessed_stats                    false
% 3.92/1.03  
% 3.92/1.03  ------ Abstraction refinement Options
% 3.92/1.03  
% 3.92/1.03  --abstr_ref                             []
% 3.92/1.03  --abstr_ref_prep                        false
% 3.92/1.03  --abstr_ref_until_sat                   false
% 3.92/1.03  --abstr_ref_sig_restrict                funpre
% 3.92/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.03  --abstr_ref_under                       []
% 3.92/1.03  
% 3.92/1.03  ------ SAT Options
% 3.92/1.03  
% 3.92/1.03  --sat_mode                              false
% 3.92/1.03  --sat_fm_restart_options                ""
% 3.92/1.03  --sat_gr_def                            false
% 3.92/1.03  --sat_epr_types                         true
% 3.92/1.03  --sat_non_cyclic_types                  false
% 3.92/1.03  --sat_finite_models                     false
% 3.92/1.03  --sat_fm_lemmas                         false
% 3.92/1.03  --sat_fm_prep                           false
% 3.92/1.03  --sat_fm_uc_incr                        true
% 3.92/1.03  --sat_out_model                         small
% 3.92/1.03  --sat_out_clauses                       false
% 3.92/1.03  
% 3.92/1.03  ------ QBF Options
% 3.92/1.03  
% 3.92/1.03  --qbf_mode                              false
% 3.92/1.03  --qbf_elim_univ                         false
% 3.92/1.03  --qbf_dom_inst                          none
% 3.92/1.03  --qbf_dom_pre_inst                      false
% 3.92/1.03  --qbf_sk_in                             false
% 3.92/1.03  --qbf_pred_elim                         true
% 3.92/1.03  --qbf_split                             512
% 3.92/1.03  
% 3.92/1.03  ------ BMC1 Options
% 3.92/1.03  
% 3.92/1.03  --bmc1_incremental                      false
% 3.92/1.03  --bmc1_axioms                           reachable_all
% 3.92/1.03  --bmc1_min_bound                        0
% 3.92/1.03  --bmc1_max_bound                        -1
% 3.92/1.03  --bmc1_max_bound_default                -1
% 3.92/1.03  --bmc1_symbol_reachability              true
% 3.92/1.03  --bmc1_property_lemmas                  false
% 3.92/1.03  --bmc1_k_induction                      false
% 3.92/1.03  --bmc1_non_equiv_states                 false
% 3.92/1.03  --bmc1_deadlock                         false
% 3.92/1.03  --bmc1_ucm                              false
% 3.92/1.03  --bmc1_add_unsat_core                   none
% 3.92/1.03  --bmc1_unsat_core_children              false
% 3.92/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.03  --bmc1_out_stat                         full
% 3.92/1.03  --bmc1_ground_init                      false
% 3.92/1.03  --bmc1_pre_inst_next_state              false
% 3.92/1.03  --bmc1_pre_inst_state                   false
% 3.92/1.03  --bmc1_pre_inst_reach_state             false
% 3.92/1.03  --bmc1_out_unsat_core                   false
% 3.92/1.03  --bmc1_aig_witness_out                  false
% 3.92/1.03  --bmc1_verbose                          false
% 3.92/1.03  --bmc1_dump_clauses_tptp                false
% 3.92/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.03  --bmc1_dump_file                        -
% 3.92/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.03  --bmc1_ucm_extend_mode                  1
% 3.92/1.03  --bmc1_ucm_init_mode                    2
% 3.92/1.03  --bmc1_ucm_cone_mode                    none
% 3.92/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.03  --bmc1_ucm_relax_model                  4
% 3.92/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.03  --bmc1_ucm_layered_model                none
% 3.92/1.03  --bmc1_ucm_max_lemma_size               10
% 3.92/1.03  
% 3.92/1.03  ------ AIG Options
% 3.92/1.03  
% 3.92/1.03  --aig_mode                              false
% 3.92/1.03  
% 3.92/1.03  ------ Instantiation Options
% 3.92/1.03  
% 3.92/1.03  --instantiation_flag                    true
% 3.92/1.03  --inst_sos_flag                         false
% 3.92/1.03  --inst_sos_phase                        true
% 3.92/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.03  --inst_lit_sel_side                     none
% 3.92/1.03  --inst_solver_per_active                1400
% 3.92/1.03  --inst_solver_calls_frac                1.
% 3.92/1.03  --inst_passive_queue_type               priority_queues
% 3.92/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.03  --inst_passive_queues_freq              [25;2]
% 3.92/1.03  --inst_dismatching                      true
% 3.92/1.03  --inst_eager_unprocessed_to_passive     true
% 3.92/1.03  --inst_prop_sim_given                   true
% 3.92/1.03  --inst_prop_sim_new                     false
% 3.92/1.03  --inst_subs_new                         false
% 3.92/1.03  --inst_eq_res_simp                      false
% 3.92/1.03  --inst_subs_given                       false
% 3.92/1.03  --inst_orphan_elimination               true
% 3.92/1.03  --inst_learning_loop_flag               true
% 3.92/1.03  --inst_learning_start                   3000
% 3.92/1.03  --inst_learning_factor                  2
% 3.92/1.03  --inst_start_prop_sim_after_learn       3
% 3.92/1.03  --inst_sel_renew                        solver
% 3.92/1.03  --inst_lit_activity_flag                true
% 3.92/1.03  --inst_restr_to_given                   false
% 3.92/1.03  --inst_activity_threshold               500
% 3.92/1.03  --inst_out_proof                        true
% 3.92/1.03  
% 3.92/1.03  ------ Resolution Options
% 3.92/1.03  
% 3.92/1.03  --resolution_flag                       false
% 3.92/1.03  --res_lit_sel                           adaptive
% 3.92/1.03  --res_lit_sel_side                      none
% 3.92/1.03  --res_ordering                          kbo
% 3.92/1.03  --res_to_prop_solver                    active
% 3.92/1.03  --res_prop_simpl_new                    false
% 3.92/1.03  --res_prop_simpl_given                  true
% 3.92/1.03  --res_passive_queue_type                priority_queues
% 3.92/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.03  --res_passive_queues_freq               [15;5]
% 3.92/1.03  --res_forward_subs                      full
% 3.92/1.03  --res_backward_subs                     full
% 3.92/1.03  --res_forward_subs_resolution           true
% 3.92/1.03  --res_backward_subs_resolution          true
% 3.92/1.03  --res_orphan_elimination                true
% 3.92/1.03  --res_time_limit                        2.
% 3.92/1.03  --res_out_proof                         true
% 3.92/1.03  
% 3.92/1.03  ------ Superposition Options
% 3.92/1.03  
% 3.92/1.03  --superposition_flag                    true
% 3.92/1.03  --sup_passive_queue_type                priority_queues
% 3.92/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.92/1.03  --demod_completeness_check              fast
% 3.92/1.03  --demod_use_ground                      true
% 3.92/1.03  --sup_to_prop_solver                    passive
% 3.92/1.03  --sup_prop_simpl_new                    true
% 3.92/1.03  --sup_prop_simpl_given                  true
% 3.92/1.03  --sup_fun_splitting                     false
% 3.92/1.03  --sup_smt_interval                      50000
% 3.92/1.03  
% 3.92/1.03  ------ Superposition Simplification Setup
% 3.92/1.03  
% 3.92/1.03  --sup_indices_passive                   []
% 3.92/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_full_bw                           [BwDemod]
% 3.92/1.03  --sup_immed_triv                        [TrivRules]
% 3.92/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_immed_bw_main                     []
% 3.92/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.03  
% 3.92/1.03  ------ Combination Options
% 3.92/1.03  
% 3.92/1.03  --comb_res_mult                         3
% 3.92/1.03  --comb_sup_mult                         2
% 3.92/1.03  --comb_inst_mult                        10
% 3.92/1.03  
% 3.92/1.03  ------ Debug Options
% 3.92/1.03  
% 3.92/1.03  --dbg_backtrace                         false
% 3.92/1.03  --dbg_dump_prop_clauses                 false
% 3.92/1.03  --dbg_dump_prop_clauses_file            -
% 3.92/1.03  --dbg_out_stat                          false
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  ------ Proving...
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  % SZS status Theorem for theBenchmark.p
% 3.92/1.03  
% 3.92/1.03   Resolution empty clause
% 3.92/1.03  
% 3.92/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/1.03  
% 3.92/1.03  fof(f18,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f35,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(ennf_transformation,[],[f18])).
% 3.92/1.03  
% 3.92/1.03  fof(f36,plain,(
% 3.92/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(flattening,[],[f35])).
% 3.92/1.03  
% 3.92/1.03  fof(f47,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(nnf_transformation,[],[f36])).
% 3.92/1.03  
% 3.92/1.03  fof(f76,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f47])).
% 3.92/1.03  
% 3.92/1.03  fof(f19,conjecture,(
% 3.92/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f20,negated_conjecture,(
% 3.92/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.92/1.03    inference(negated_conjecture,[],[f19])).
% 3.92/1.03  
% 3.92/1.03  fof(f37,plain,(
% 3.92/1.03    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.92/1.03    inference(ennf_transformation,[],[f20])).
% 3.92/1.03  
% 3.92/1.03  fof(f38,plain,(
% 3.92/1.03    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.92/1.03    inference(flattening,[],[f37])).
% 3.92/1.03  
% 3.92/1.03  fof(f48,plain,(
% 3.92/1.03    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.92/1.03    introduced(choice_axiom,[])).
% 3.92/1.03  
% 3.92/1.03  fof(f49,plain,(
% 3.92/1.03    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.92/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f48])).
% 3.92/1.03  
% 3.92/1.03  fof(f83,plain,(
% 3.92/1.03    v1_funct_2(sK4,sK1,sK2)),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f84,plain,(
% 3.92/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f14,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f30,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(ennf_transformation,[],[f14])).
% 3.92/1.03  
% 3.92/1.03  fof(f70,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f30])).
% 3.92/1.03  
% 3.92/1.03  fof(f13,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f21,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.92/1.03    inference(pure_predicate_removal,[],[f13])).
% 3.92/1.03  
% 3.92/1.03  fof(f29,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(ennf_transformation,[],[f21])).
% 3.92/1.03  
% 3.92/1.03  fof(f69,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f29])).
% 3.92/1.03  
% 3.92/1.03  fof(f9,axiom,(
% 3.92/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f25,plain,(
% 3.92/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.92/1.03    inference(ennf_transformation,[],[f9])).
% 3.92/1.03  
% 3.92/1.03  fof(f44,plain,(
% 3.92/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.92/1.03    inference(nnf_transformation,[],[f25])).
% 3.92/1.03  
% 3.92/1.03  fof(f63,plain,(
% 3.92/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f44])).
% 3.92/1.03  
% 3.92/1.03  fof(f15,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f31,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.92/1.03    inference(ennf_transformation,[],[f15])).
% 3.92/1.03  
% 3.92/1.03  fof(f71,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f31])).
% 3.92/1.03  
% 3.92/1.03  fof(f85,plain,(
% 3.92/1.03    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f16,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f32,plain,(
% 3.92/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.92/1.03    inference(ennf_transformation,[],[f16])).
% 3.92/1.03  
% 3.92/1.03  fof(f33,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.92/1.03    inference(flattening,[],[f32])).
% 3.92/1.03  
% 3.92/1.03  fof(f72,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f33])).
% 3.92/1.03  
% 3.92/1.03  fof(f6,axiom,(
% 3.92/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f43,plain,(
% 3.92/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.92/1.03    inference(nnf_transformation,[],[f6])).
% 3.92/1.03  
% 3.92/1.03  fof(f59,plain,(
% 3.92/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f43])).
% 3.92/1.03  
% 3.92/1.03  fof(f8,axiom,(
% 3.92/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f24,plain,(
% 3.92/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.92/1.03    inference(ennf_transformation,[],[f8])).
% 3.92/1.03  
% 3.92/1.03  fof(f62,plain,(
% 3.92/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f24])).
% 3.92/1.03  
% 3.92/1.03  fof(f60,plain,(
% 3.92/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f43])).
% 3.92/1.03  
% 3.92/1.03  fof(f11,axiom,(
% 3.92/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f66,plain,(
% 3.92/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f11])).
% 3.92/1.03  
% 3.92/1.03  fof(f78,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f47])).
% 3.92/1.03  
% 3.92/1.03  fof(f87,plain,(
% 3.92/1.03    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f82,plain,(
% 3.92/1.03    v1_funct_1(sK4)),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f86,plain,(
% 3.92/1.03    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.92/1.03    inference(cnf_transformation,[],[f49])).
% 3.92/1.03  
% 3.92/1.03  fof(f1,axiom,(
% 3.92/1.03    v1_xboole_0(k1_xboole_0)),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f50,plain,(
% 3.92/1.03    v1_xboole_0(k1_xboole_0)),
% 3.92/1.03    inference(cnf_transformation,[],[f1])).
% 3.92/1.03  
% 3.92/1.03  fof(f3,axiom,(
% 3.92/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f39,plain,(
% 3.92/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/1.03    inference(nnf_transformation,[],[f3])).
% 3.92/1.03  
% 3.92/1.03  fof(f40,plain,(
% 3.92/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/1.03    inference(flattening,[],[f39])).
% 3.92/1.03  
% 3.92/1.03  fof(f54,plain,(
% 3.92/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f40])).
% 3.92/1.03  
% 3.92/1.03  fof(f52,plain,(
% 3.92/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.92/1.03    inference(cnf_transformation,[],[f40])).
% 3.92/1.03  
% 3.92/1.03  fof(f89,plain,(
% 3.92/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.92/1.03    inference(equality_resolution,[],[f52])).
% 3.92/1.03  
% 3.92/1.03  fof(f7,axiom,(
% 3.92/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f23,plain,(
% 3.92/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.92/1.03    inference(ennf_transformation,[],[f7])).
% 3.92/1.03  
% 3.92/1.03  fof(f61,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f23])).
% 3.92/1.03  
% 3.92/1.03  fof(f17,axiom,(
% 3.92/1.03    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f34,plain,(
% 3.92/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.92/1.03    inference(ennf_transformation,[],[f17])).
% 3.92/1.03  
% 3.92/1.03  fof(f45,plain,(
% 3.92/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.92/1.03    introduced(choice_axiom,[])).
% 3.92/1.03  
% 3.92/1.03  fof(f46,plain,(
% 3.92/1.03    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.92/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f45])).
% 3.92/1.03  
% 3.92/1.03  fof(f73,plain,(
% 3.92/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.92/1.03    inference(cnf_transformation,[],[f46])).
% 3.92/1.03  
% 3.92/1.03  fof(f12,axiom,(
% 3.92/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f27,plain,(
% 3.92/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.92/1.03    inference(ennf_transformation,[],[f12])).
% 3.92/1.03  
% 3.92/1.03  fof(f28,plain,(
% 3.92/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.92/1.03    inference(flattening,[],[f27])).
% 3.92/1.03  
% 3.92/1.03  fof(f68,plain,(
% 3.92/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f28])).
% 3.92/1.03  
% 3.92/1.03  fof(f5,axiom,(
% 3.92/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f41,plain,(
% 3.92/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.92/1.03    inference(nnf_transformation,[],[f5])).
% 3.92/1.03  
% 3.92/1.03  fof(f42,plain,(
% 3.92/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.92/1.03    inference(flattening,[],[f41])).
% 3.92/1.03  
% 3.92/1.03  fof(f57,plain,(
% 3.92/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.92/1.03    inference(cnf_transformation,[],[f42])).
% 3.92/1.03  
% 3.92/1.03  fof(f91,plain,(
% 3.92/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.92/1.03    inference(equality_resolution,[],[f57])).
% 3.92/1.03  
% 3.92/1.03  fof(f56,plain,(
% 3.92/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f42])).
% 3.92/1.03  
% 3.92/1.03  fof(f4,axiom,(
% 3.92/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.92/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/1.03  
% 3.92/1.03  fof(f55,plain,(
% 3.92/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.92/1.03    inference(cnf_transformation,[],[f4])).
% 3.92/1.03  
% 3.92/1.03  fof(f80,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f47])).
% 3.92/1.03  
% 3.92/1.03  fof(f94,plain,(
% 3.92/1.03    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.92/1.03    inference(equality_resolution,[],[f80])).
% 3.92/1.03  
% 3.92/1.03  fof(f58,plain,(
% 3.92/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.92/1.03    inference(cnf_transformation,[],[f42])).
% 3.92/1.03  
% 3.92/1.03  fof(f90,plain,(
% 3.92/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.92/1.03    inference(equality_resolution,[],[f58])).
% 3.92/1.03  
% 3.92/1.03  fof(f77,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f47])).
% 3.92/1.03  
% 3.92/1.03  fof(f96,plain,(
% 3.92/1.03    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.92/1.03    inference(equality_resolution,[],[f77])).
% 3.92/1.03  
% 3.92/1.03  fof(f79,plain,(
% 3.92/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.92/1.03    inference(cnf_transformation,[],[f47])).
% 3.92/1.03  
% 3.92/1.03  fof(f95,plain,(
% 3.92/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.92/1.03    inference(equality_resolution,[],[f79])).
% 3.92/1.03  
% 3.92/1.03  cnf(c_31,plain,
% 3.92/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.92/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.92/1.03      | k1_xboole_0 = X2 ),
% 3.92/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_36,negated_conjecture,
% 3.92/1.03      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.92/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_599,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.92/1.03      | sK2 != X2
% 3.92/1.03      | sK1 != X1
% 3.92/1.03      | sK4 != X0
% 3.92/1.03      | k1_xboole_0 = X2 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_600,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.92/1.03      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.92/1.03      | k1_xboole_0 = sK2 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_599]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_35,negated_conjecture,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.92/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_602,plain,
% 3.92/1.03      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.92/1.03      inference(global_propositional_subsumption,[status(thm)],[c_600,c_35]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1491,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_20,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1495,plain,
% 3.92/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.92/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3761,plain,
% 3.92/1.03      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1491,c_1495]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3936,plain,
% 3.92/1.03      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_602,c_3761]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_19,plain,
% 3.92/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.92/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14,plain,
% 3.92/1.03      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_448,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.92/1.03      | ~ v1_relat_1(X0) ),
% 3.92/1.03      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1489,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.92/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3701,plain,
% 3.92/1.03      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 3.92/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1491,c_1489]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_21,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1494,plain,
% 3.92/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.92/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3173,plain,
% 3.92/1.03      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1491,c_1494]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_34,negated_conjecture,
% 3.92/1.03      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.92/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1492,plain,
% 3.92/1.03      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3324,plain,
% 3.92/1.03      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_3173,c_1492]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_22,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.92/1.03      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.92/1.03      | ~ v1_relat_1(X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1493,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.92/1.03      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.92/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4587,plain,
% 3.92/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.92/1.03      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.92/1.03      | v1_relat_1(X2) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1493,c_1495]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_13832,plain,
% 3.92/1.03      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.92/1.03      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.92/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_3324,c_4587]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_10,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.92/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1500,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.92/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2468,plain,
% 3.92/1.03      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1491,c_1500]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_12,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_9,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.92/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_272,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.92/1.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_273,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_272]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_335,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.92/1.03      inference(bin_hyper_res,[status(thm)],[c_12,c_273]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1490,plain,
% 3.92/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.92/1.03      | v1_relat_1(X1) != iProver_top
% 3.92/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4451,plain,
% 3.92/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.92/1.03      | v1_relat_1(sK4) = iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_2468,c_1490]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_16,plain,
% 3.92/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.92/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1498,plain,
% 3.92/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4858,plain,
% 3.92/1.03      ( v1_relat_1(sK4) = iProver_top ),
% 3.92/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4451,c_1498]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14320,plain,
% 3.92/1.03      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.92/1.03      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_13832,c_4858]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14321,plain,
% 3.92/1.03      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.92/1.03      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_14320]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14331,plain,
% 3.92/1.03      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
% 3.92/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_3701,c_14321]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14382,plain,
% 3.92/1.03      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_14331,c_4858]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_29,plain,
% 3.92/1.03      ( v1_funct_2(X0,X1,X2)
% 3.92/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | k1_relset_1(X1,X2,X0) != X1
% 3.92/1.03      | k1_xboole_0 = X2 ),
% 3.92/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_32,negated_conjecture,
% 3.92/1.03      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.92/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | ~ v1_funct_1(sK4) ),
% 3.92/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_37,negated_conjecture,
% 3.92/1.03      ( v1_funct_1(sK4) ),
% 3.92/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_195,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.92/1.03      inference(global_propositional_subsumption,[status(thm)],[c_32,c_37]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_196,negated_conjecture,
% 3.92/1.03      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.92/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_195]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_586,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.92/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | k1_relset_1(X1,X2,X0) != X1
% 3.92/1.03      | sK3 != X2
% 3.92/1.03      | sK1 != X1
% 3.92/1.03      | sK4 != X0
% 3.92/1.03      | k1_xboole_0 = X2 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_29,c_196]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_587,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.92/1.03      | k1_xboole_0 = sK3 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_586]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1484,plain,
% 3.92/1.03      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.92/1.03      | k1_xboole_0 = sK3
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14385,plain,
% 3.92/1.03      ( k1_relat_1(sK4) != sK1
% 3.92/1.03      | sK3 = k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14382,c_1484]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2142,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.92/1.03      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 3.92/1.03      | ~ v1_relat_1(sK4) ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_22]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2143,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.92/1.03      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 3.92/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_2142]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14492,plain,
% 3.92/1.03      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) != sK1 ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_14385,c_2143,c_3324,c_3701,c_4858]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14493,plain,
% 3.92/1.03      ( k1_relat_1(sK4) != sK1 | sK3 = k1_xboole_0 ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_14492]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14496,plain,
% 3.92/1.03      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_3936,c_14493]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_33,negated_conjecture,
% 3.92/1.03      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.92/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14508,plain,
% 3.92/1.03      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_14496,c_33]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_0,plain,
% 3.92/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.92/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1736,plain,
% 3.92/1.03      ( ~ r1_tarski(sK1,k1_xboole_0)
% 3.92/1.03      | ~ r1_tarski(k1_xboole_0,sK1)
% 3.92/1.03      | sK1 = k1_xboole_0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_887,plain,( X0 = X0 ),theory(equality) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2051,plain,
% 3.92/1.03      ( sK4 = sK4 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_887]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f89]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2853,plain,
% 3.92/1.03      ( r1_tarski(sK4,sK4) ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_11,plain,
% 3.92/1.03      ( ~ r2_hidden(X0,X1)
% 3.92/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.92/1.03      | ~ v1_xboole_0(X2) ),
% 3.92/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_25,plain,
% 3.92/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_485,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.92/1.03      | ~ v1_xboole_0(X1)
% 3.92/1.03      | X2 != X0
% 3.92/1.03      | sK0(X2) != X3
% 3.92/1.03      | k1_xboole_0 = X2 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_486,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.92/1.03      | ~ v1_xboole_0(X1)
% 3.92/1.03      | k1_xboole_0 = X0 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_485]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_741,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.92/1.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_742,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_741]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_798,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 3.92/1.03      inference(bin_hyper_res,[status(thm)],[c_486,c_742]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1482,plain,
% 3.92/1.03      ( k1_xboole_0 = X0
% 3.92/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.92/1.03      | v1_xboole_0(X1) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3328,plain,
% 3.92/1.03      ( k2_relat_1(sK4) = k1_xboole_0 | v1_xboole_0(sK3) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_3324,c_1482]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3329,plain,
% 3.92/1.03      ( ~ v1_xboole_0(sK3) | k2_relat_1(sK4) = k1_xboole_0 ),
% 3.92/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3328]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4859,plain,
% 3.92/1.03      ( v1_relat_1(sK4) ),
% 3.92/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4858]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_889,plain,
% 3.92/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.92/1.03      theory(equality) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4889,plain,
% 3.92/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_889]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_4891,plain,
% 3.92/1.03      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_4889]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_17,plain,
% 3.92/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_5625,plain,
% 3.92/1.03      ( ~ v1_relat_1(sK4)
% 3.92/1.03      | k2_relat_1(sK4) != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 = sK4 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7,plain,
% 3.92/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1501,plain,
% 3.92/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.92/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_3700,plain,
% 3.92/1.03      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.92/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_1501,c_1489]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7105,plain,
% 3.92/1.03      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.92/1.03      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 3.92/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_7,c_3700]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7139,plain,
% 3.92/1.03      ( sK2 = k1_xboole_0
% 3.92/1.03      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.92/1.03      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.92/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.92/1.03      inference(superposition,[status(thm)],[c_3936,c_7105]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_8,plain,
% 3.92/1.03      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 = X0
% 3.92/1.03      | k1_xboole_0 = X1 ),
% 3.92/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_108,plain,
% 3.92/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_109,plain,
% 3.92/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_5,plain,
% 3.92/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.92/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_110,plain,
% 3.92/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_112,plain,
% 3.92/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_110]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_890,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/1.03      theory(equality) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1798,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1)
% 3.92/1.03      | r1_tarski(sK1,k1_xboole_0)
% 3.92/1.03      | sK1 != X0
% 3.92/1.03      | k1_xboole_0 != X1 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_890]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1799,plain,
% 3.92/1.03      ( sK1 != X0
% 3.92/1.03      | k1_xboole_0 != X1
% 3.92/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.92/1.03      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1801,plain,
% 3.92/1.03      ( sK1 != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 != k1_xboole_0
% 3.92/1.03      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.92/1.03      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_1799]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_27,plain,
% 3.92/1.03      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.92/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.92/1.03      | k1_xboole_0 = X1
% 3.92/1.03      | k1_xboole_0 = X0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_537,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.92/1.03      | sK2 != k1_xboole_0
% 3.92/1.03      | sK1 != X1
% 3.92/1.03      | sK4 != X0
% 3.92/1.03      | k1_xboole_0 = X0
% 3.92/1.03      | k1_xboole_0 = X1 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_538,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.92/1.03      | sK2 != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 = sK1
% 3.92/1.03      | k1_xboole_0 = sK4 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_537]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1487,plain,
% 3.92/1.03      ( sK2 != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 = sK1
% 3.92/1.03      | k1_xboole_0 = sK4
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_6,plain,
% 3.92/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1616,plain,
% 3.92/1.03      ( sK2 != k1_xboole_0
% 3.92/1.03      | sK1 = k1_xboole_0
% 3.92/1.03      | sK4 = k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_1487,c_6]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_888,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1747,plain,
% 3.92/1.03      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_888]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1806,plain,
% 3.92/1.03      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_1747]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1807,plain,
% 3.92/1.03      ( sK1 = sK1 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_887]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2018,plain,
% 3.92/1.03      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_888]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2019,plain,
% 3.92/1.03      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_2018]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2131,plain,
% 3.92/1.03      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_1616,c_33,c_108,c_109,c_1806,c_1807,c_2019]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7528,plain,
% 3.92/1.03      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.92/1.03      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_7139,c_108,c_109,c_112,c_1801,c_2131,c_4858]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7529,plain,
% 3.92/1.03      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.92/1.03      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.92/1.03      inference(renaming,[status(thm)],[c_7528]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_7530,plain,
% 3.92/1.03      ( r1_tarski(sK1,k1_xboole_0) | ~ r1_tarski(sK4,k1_xboole_0) ),
% 3.92/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_7529]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_8401,plain,
% 3.92/1.03      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_2868,plain,
% 3.92/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_890]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_6177,plain,
% 3.92/1.03      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_2868]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_12253,plain,
% 3.92/1.03      ( r1_tarski(sK4,X0) | ~ r1_tarski(sK4,sK4) | X0 != sK4 | sK4 != sK4 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_6177]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_12255,plain,
% 3.92/1.03      ( ~ r1_tarski(sK4,sK4)
% 3.92/1.03      | r1_tarski(sK4,k1_xboole_0)
% 3.92/1.03      | sK4 != sK4
% 3.92/1.03      | k1_xboole_0 != sK4 ),
% 3.92/1.03      inference(instantiation,[status(thm)],[c_12253]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14639,plain,
% 3.92/1.03      ( sK1 = k1_xboole_0 ),
% 3.92/1.03      inference(global_propositional_subsumption,
% 3.92/1.03                [status(thm)],
% 3.92/1.03                [c_14508,c_0,c_1736,c_2051,c_2853,c_3329,c_4859,c_4891,
% 3.92/1.03                 c_5625,c_7530,c_8401,c_12255]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14643,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14639,c_14382]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14714,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14639,c_3761]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_30,plain,
% 3.92/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.92/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_573,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.92/1.03      | sK2 != X1
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | sK4 != X0 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_574,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_573]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1485,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1609,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_1485,c_7]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14721,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.92/1.03      | k1_xboole_0 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14639,c_1609]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14738,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(equality_resolution_simp,[status(thm)],[c_14721]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14724,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14639,c_1491]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14727,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14724,c_7]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14741,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
% 3.92/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_14738,c_14727]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14761,plain,
% 3.92/1.03      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.92/1.03      inference(light_normalisation,[status(thm)],[c_14714,c_14741]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14971,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
% 3.92/1.03      inference(light_normalisation,[status(thm)],[c_14643,c_14761]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_28,plain,
% 3.92/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.92/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.92/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_557,plain,
% 3.92/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.92/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.92/1.03      | sK3 != X1
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | sK4 != X0 ),
% 3.92/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_196]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_558,plain,
% 3.92/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.92/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.92/1.03      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0 ),
% 3.92/1.03      inference(unflattening,[status(thm)],[c_557]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1486,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.92/1.03      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_1639,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | sK1 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_1486,c_7]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14720,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | k1_xboole_0 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14639,c_1639]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14743,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(equality_resolution_simp,[status(thm)],[c_14720]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14747,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.92/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_14743,c_14727]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14748,plain,
% 3.92/1.03      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14747,c_7]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14973,plain,
% 3.92/1.03      ( k1_xboole_0 != k1_xboole_0
% 3.92/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(demodulation,[status(thm)],[c_14971,c_14748]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14975,plain,
% 3.92/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.92/1.03      inference(equality_resolution_simp,[status(thm)],[c_14973]) ).
% 3.92/1.03  
% 3.92/1.03  cnf(c_14977,plain,
% 3.92/1.03      ( $false ),
% 3.92/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_14975,c_14727]) ).
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/1.03  
% 3.92/1.03  ------                               Statistics
% 3.92/1.03  
% 3.92/1.03  ------ General
% 3.92/1.03  
% 3.92/1.03  abstr_ref_over_cycles:                  0
% 3.92/1.03  abstr_ref_under_cycles:                 0
% 3.92/1.03  gc_basic_clause_elim:                   0
% 3.92/1.03  forced_gc_time:                         0
% 3.92/1.03  parsing_time:                           0.011
% 3.92/1.03  unif_index_cands_time:                  0.
% 3.92/1.03  unif_index_add_time:                    0.
% 3.92/1.03  orderings_time:                         0.
% 3.92/1.03  out_proof_time:                         0.012
% 3.92/1.03  total_time:                             0.397
% 3.92/1.03  num_of_symbols:                         52
% 3.92/1.03  num_of_terms:                           10721
% 3.92/1.03  
% 3.92/1.03  ------ Preprocessing
% 3.92/1.03  
% 3.92/1.03  num_of_splits:                          0
% 3.92/1.03  num_of_split_atoms:                     0
% 3.92/1.03  num_of_reused_defs:                     0
% 3.92/1.03  num_eq_ax_congr_red:                    19
% 3.92/1.03  num_of_sem_filtered_clauses:            2
% 3.92/1.03  num_of_subtypes:                        0
% 3.92/1.03  monotx_restored_types:                  0
% 3.92/1.03  sat_num_of_epr_types:                   0
% 3.92/1.03  sat_num_of_non_cyclic_types:            0
% 3.92/1.03  sat_guarded_non_collapsed_types:        0
% 3.92/1.03  num_pure_diseq_elim:                    0
% 3.92/1.03  simp_replaced_by:                       0
% 3.92/1.03  res_preprocessed:                       156
% 3.92/1.03  prep_upred:                             0
% 3.92/1.03  prep_unflattend:                        39
% 3.92/1.03  smt_new_axioms:                         0
% 3.92/1.03  pred_elim_cands:                        4
% 3.92/1.03  pred_elim:                              3
% 3.92/1.03  pred_elim_cl:                           4
% 3.92/1.03  pred_elim_cycles:                       5
% 3.92/1.03  merged_defs:                            8
% 3.92/1.03  merged_defs_ncl:                        0
% 3.92/1.03  bin_hyper_res:                          10
% 3.92/1.03  prep_cycles:                            4
% 3.92/1.03  pred_elim_time:                         0.006
% 3.92/1.03  splitting_time:                         0.
% 3.92/1.03  sem_filter_time:                        0.
% 3.92/1.03  monotx_time:                            0.
% 3.92/1.03  subtype_inf_time:                       0.
% 3.92/1.03  
% 3.92/1.03  ------ Problem properties
% 3.92/1.03  
% 3.92/1.03  clauses:                                32
% 3.92/1.03  conjectures:                            3
% 3.92/1.03  epr:                                    8
% 3.92/1.03  horn:                                   29
% 3.92/1.03  ground:                                 11
% 3.92/1.03  unary:                                  8
% 3.92/1.03  binary:                                 11
% 3.92/1.03  lits:                                   74
% 3.92/1.03  lits_eq:                                35
% 3.92/1.03  fd_pure:                                0
% 3.92/1.03  fd_pseudo:                              0
% 3.92/1.03  fd_cond:                                7
% 3.92/1.03  fd_pseudo_cond:                         1
% 3.92/1.03  ac_symbols:                             0
% 3.92/1.03  
% 3.92/1.03  ------ Propositional Solver
% 3.92/1.03  
% 3.92/1.03  prop_solver_calls:                      29
% 3.92/1.03  prop_fast_solver_calls:                 1442
% 3.92/1.03  smt_solver_calls:                       0
% 3.92/1.03  smt_fast_solver_calls:                  0
% 3.92/1.03  prop_num_of_clauses:                    5072
% 3.92/1.03  prop_preprocess_simplified:             9683
% 3.92/1.03  prop_fo_subsumed:                       50
% 3.92/1.03  prop_solver_time:                       0.
% 3.92/1.03  smt_solver_time:                        0.
% 3.92/1.03  smt_fast_solver_time:                   0.
% 3.92/1.03  prop_fast_solver_time:                  0.
% 3.92/1.03  prop_unsat_core_time:                   0.
% 3.92/1.03  
% 3.92/1.03  ------ QBF
% 3.92/1.03  
% 3.92/1.03  qbf_q_res:                              0
% 3.92/1.03  qbf_num_tautologies:                    0
% 3.92/1.03  qbf_prep_cycles:                        0
% 3.92/1.03  
% 3.92/1.03  ------ BMC1
% 3.92/1.03  
% 3.92/1.03  bmc1_current_bound:                     -1
% 3.92/1.03  bmc1_last_solved_bound:                 -1
% 3.92/1.03  bmc1_unsat_core_size:                   -1
% 3.92/1.03  bmc1_unsat_core_parents_size:           -1
% 3.92/1.03  bmc1_merge_next_fun:                    0
% 3.92/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.92/1.03  
% 3.92/1.03  ------ Instantiation
% 3.92/1.03  
% 3.92/1.03  inst_num_of_clauses:                    1480
% 3.92/1.03  inst_num_in_passive:                    56
% 3.92/1.03  inst_num_in_active:                     774
% 3.92/1.03  inst_num_in_unprocessed:                652
% 3.92/1.03  inst_num_of_loops:                      930
% 3.92/1.03  inst_num_of_learning_restarts:          0
% 3.92/1.03  inst_num_moves_active_passive:          152
% 3.92/1.03  inst_lit_activity:                      0
% 3.92/1.03  inst_lit_activity_moves:                0
% 3.92/1.03  inst_num_tautologies:                   0
% 3.92/1.03  inst_num_prop_implied:                  0
% 3.92/1.03  inst_num_existing_simplified:           0
% 3.92/1.03  inst_num_eq_res_simplified:             0
% 3.92/1.03  inst_num_child_elim:                    0
% 3.92/1.03  inst_num_of_dismatching_blockings:      692
% 3.92/1.03  inst_num_of_non_proper_insts:           2200
% 3.92/1.03  inst_num_of_duplicates:                 0
% 3.92/1.03  inst_inst_num_from_inst_to_res:         0
% 3.92/1.03  inst_dismatching_checking_time:         0.
% 3.92/1.03  
% 3.92/1.03  ------ Resolution
% 3.92/1.03  
% 3.92/1.03  res_num_of_clauses:                     0
% 3.92/1.03  res_num_in_passive:                     0
% 3.92/1.03  res_num_in_active:                      0
% 3.92/1.03  res_num_of_loops:                       160
% 3.92/1.03  res_forward_subset_subsumed:            136
% 3.92/1.03  res_backward_subset_subsumed:           6
% 3.92/1.03  res_forward_subsumed:                   0
% 3.92/1.03  res_backward_subsumed:                  0
% 3.92/1.03  res_forward_subsumption_resolution:     0
% 3.92/1.03  res_backward_subsumption_resolution:    0
% 3.92/1.03  res_clause_to_clause_subsumption:       2156
% 3.92/1.03  res_orphan_elimination:                 0
% 3.92/1.03  res_tautology_del:                      177
% 3.92/1.03  res_num_eq_res_simplified:              1
% 3.92/1.03  res_num_sel_changes:                    0
% 3.92/1.03  res_moves_from_active_to_pass:          0
% 3.92/1.03  
% 3.92/1.03  ------ Superposition
% 3.92/1.03  
% 3.92/1.03  sup_time_total:                         0.
% 3.92/1.03  sup_time_generating:                    0.
% 3.92/1.03  sup_time_sim_full:                      0.
% 3.92/1.03  sup_time_sim_immed:                     0.
% 3.92/1.03  
% 3.92/1.03  sup_num_of_clauses:                     160
% 3.92/1.03  sup_num_in_active:                      95
% 3.92/1.03  sup_num_in_passive:                     65
% 3.92/1.03  sup_num_of_loops:                       184
% 3.92/1.03  sup_fw_superposition:                   306
% 3.92/1.03  sup_bw_superposition:                   153
% 3.92/1.03  sup_immediate_simplified:               125
% 3.92/1.03  sup_given_eliminated:                   3
% 3.92/1.03  comparisons_done:                       0
% 3.92/1.03  comparisons_avoided:                    108
% 3.92/1.03  
% 3.92/1.03  ------ Simplifications
% 3.92/1.03  
% 3.92/1.03  
% 3.92/1.03  sim_fw_subset_subsumed:                 34
% 3.92/1.03  sim_bw_subset_subsumed:                 2
% 3.92/1.03  sim_fw_subsumed:                        43
% 3.92/1.03  sim_bw_subsumed:                        32
% 3.92/1.03  sim_fw_subsumption_res:                 8
% 3.92/1.03  sim_bw_subsumption_res:                 0
% 3.92/1.03  sim_tautology_del:                      14
% 3.92/1.03  sim_eq_tautology_del:                   70
% 3.92/1.03  sim_eq_res_simp:                        4
% 3.92/1.03  sim_fw_demodulated:                     30
% 3.92/1.03  sim_bw_demodulated:                     87
% 3.92/1.03  sim_light_normalised:                   99
% 3.92/1.03  sim_joinable_taut:                      0
% 3.92/1.03  sim_joinable_simp:                      0
% 3.92/1.03  sim_ac_normalised:                      0
% 3.92/1.03  sim_smt_subsumption:                    0
% 3.92/1.03  
%------------------------------------------------------------------------------
