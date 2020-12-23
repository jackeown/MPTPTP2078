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
% DateTime   : Thu Dec  3 12:00:38 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 655 expanded)
%              Number of clauses        :  113 ( 253 expanded)
%              Number of leaves         :   24 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  618 (3180 expanded)
%              Number of equality atoms :  234 ( 900 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f58,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f58])).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f109,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f100,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f49])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2311,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2300,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_16])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_561,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_21])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_2297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_4819,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2297])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2310,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5362,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4819,c_2310])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_45,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_230,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_41])).

cnf(c_231,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_578,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_41])).

cnf(c_579,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),X0)
    | ~ r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_956,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != sK2
    | sK4 != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_231,c_579])).

cnf(c_957,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_967,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_957,c_21,c_562])).

cnf(c_970,plain,
    ( k1_relat_1(sK5) != sK2
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_2606,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | r1_tarski(k2_relat_1(sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_2607,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2688,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2689,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2688])).

cnf(c_2651,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(X2),X0)
    | r1_tarski(k2_relat_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3251,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK5),X0)
    | r1_tarski(k2_relat_1(sK5),X1) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_3515,plain,
    ( r1_tarski(k2_relat_1(sK5),X0)
    | ~ r1_tarski(k2_relat_1(sK5),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3251])).

cnf(c_3516,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3515])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_40])).

cnf(c_907,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_909,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_907,c_39])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2303,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3780,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2300,c_2303])).

cnf(c_4126,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_909,c_3780])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_112,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_118,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_117,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_132,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1535,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2625,plain,
    ( k1_relat_1(sK5) != X0
    | k1_relat_1(sK5) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2626,plain,
    ( k1_relat_1(sK5) = sK2
    | k1_relat_1(sK5) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2625])).

cnf(c_2621,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2773,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_1534,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2774,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_40])).

cnf(c_803,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_2291,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2934,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2935,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2934])).

cnf(c_3006,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_37,c_112,c_118,c_132,c_2935])).

cnf(c_1537,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3357,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_3358,plain,
    ( sK3 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3357])).

cnf(c_3360,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3358])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_521,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_522,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_3420,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_3421,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3420])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2313,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_608,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_2295,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_610,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_2586,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2587,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2586])).

cnf(c_2628,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_44,c_610,c_2587])).

cnf(c_2629,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_2628])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2314,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3214,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_2314])).

cnf(c_3558,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_3214])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3948,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2304])).

cnf(c_4457,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_112,c_113,c_118,c_119,c_132,c_2626,c_2773,c_2774,c_3006,c_3360,c_3421,c_3558,c_3948])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_594,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | ~ r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_2296,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_595,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2637,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2296,c_44,c_595,c_2587])).

cnf(c_2638,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2637])).

cnf(c_4472,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4457,c_2638])).

cnf(c_5226,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK3)
    | r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3515])).

cnf(c_5227,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5226])).

cnf(c_5746,plain,
    ( r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5362,c_44,c_45,c_112,c_113,c_118,c_119,c_132,c_970,c_2607,c_2626,c_2689,c_2773,c_2774,c_3006,c_3360,c_3421,c_3516,c_3558,c_3948,c_4126,c_4472,c_5227])).

cnf(c_5753,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2311,c_5746])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:11:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.58/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/0.98  
% 2.58/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/0.98  
% 2.58/0.98  ------  iProver source info
% 2.58/0.98  
% 2.58/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.58/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/0.98  git: non_committed_changes: false
% 2.58/0.98  git: last_make_outside_of_git: false
% 2.58/0.98  
% 2.58/0.98  ------ 
% 2.58/0.98  
% 2.58/0.98  ------ Input Options
% 2.58/0.98  
% 2.58/0.98  --out_options                           all
% 2.58/0.98  --tptp_safe_out                         true
% 2.58/0.98  --problem_path                          ""
% 2.58/0.98  --include_path                          ""
% 2.58/0.98  --clausifier                            res/vclausify_rel
% 2.58/0.98  --clausifier_options                    --mode clausify
% 2.58/0.98  --stdin                                 false
% 2.58/0.98  --stats_out                             all
% 2.58/0.98  
% 2.58/0.98  ------ General Options
% 2.58/0.98  
% 2.58/0.98  --fof                                   false
% 2.58/0.98  --time_out_real                         305.
% 2.58/0.98  --time_out_virtual                      -1.
% 2.58/0.98  --symbol_type_check                     false
% 2.58/0.98  --clausify_out                          false
% 2.58/0.98  --sig_cnt_out                           false
% 2.58/0.98  --trig_cnt_out                          false
% 2.58/0.98  --trig_cnt_out_tolerance                1.
% 2.58/0.98  --trig_cnt_out_sk_spl                   false
% 2.58/0.98  --abstr_cl_out                          false
% 2.58/0.98  
% 2.58/0.98  ------ Global Options
% 2.58/0.98  
% 2.58/0.98  --schedule                              default
% 2.58/0.98  --add_important_lit                     false
% 2.58/0.98  --prop_solver_per_cl                    1000
% 2.58/0.98  --min_unsat_core                        false
% 2.58/0.98  --soft_assumptions                      false
% 2.58/0.98  --soft_lemma_size                       3
% 2.58/0.98  --prop_impl_unit_size                   0
% 2.58/0.98  --prop_impl_unit                        []
% 2.58/0.98  --share_sel_clauses                     true
% 2.58/0.98  --reset_solvers                         false
% 2.58/0.98  --bc_imp_inh                            [conj_cone]
% 2.58/0.98  --conj_cone_tolerance                   3.
% 2.58/0.98  --extra_neg_conj                        none
% 2.58/0.98  --large_theory_mode                     true
% 2.58/0.98  --prolific_symb_bound                   200
% 2.58/0.98  --lt_threshold                          2000
% 2.58/0.98  --clause_weak_htbl                      true
% 2.58/0.98  --gc_record_bc_elim                     false
% 2.58/0.98  
% 2.58/0.98  ------ Preprocessing Options
% 2.58/0.98  
% 2.58/0.98  --preprocessing_flag                    true
% 2.58/0.98  --time_out_prep_mult                    0.1
% 2.58/0.98  --splitting_mode                        input
% 2.58/0.98  --splitting_grd                         true
% 2.58/0.98  --splitting_cvd                         false
% 2.58/0.98  --splitting_cvd_svl                     false
% 2.58/0.98  --splitting_nvd                         32
% 2.58/0.98  --sub_typing                            true
% 2.58/0.98  --prep_gs_sim                           true
% 2.58/0.98  --prep_unflatten                        true
% 2.58/0.98  --prep_res_sim                          true
% 2.58/0.98  --prep_upred                            true
% 2.58/0.98  --prep_sem_filter                       exhaustive
% 2.58/0.98  --prep_sem_filter_out                   false
% 2.58/0.98  --pred_elim                             true
% 2.58/0.98  --res_sim_input                         true
% 2.58/0.98  --eq_ax_congr_red                       true
% 2.58/0.98  --pure_diseq_elim                       true
% 2.58/0.98  --brand_transform                       false
% 2.58/0.98  --non_eq_to_eq                          false
% 2.58/0.98  --prep_def_merge                        true
% 2.58/0.98  --prep_def_merge_prop_impl              false
% 2.58/0.98  --prep_def_merge_mbd                    true
% 2.58/0.98  --prep_def_merge_tr_red                 false
% 2.58/0.98  --prep_def_merge_tr_cl                  false
% 2.58/0.98  --smt_preprocessing                     true
% 2.58/0.98  --smt_ac_axioms                         fast
% 2.58/0.98  --preprocessed_out                      false
% 2.58/0.98  --preprocessed_stats                    false
% 2.58/0.98  
% 2.58/0.98  ------ Abstraction refinement Options
% 2.58/0.98  
% 2.58/0.98  --abstr_ref                             []
% 2.58/0.98  --abstr_ref_prep                        false
% 2.58/0.98  --abstr_ref_until_sat                   false
% 2.58/0.98  --abstr_ref_sig_restrict                funpre
% 2.58/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.98  --abstr_ref_under                       []
% 2.58/0.98  
% 2.58/0.98  ------ SAT Options
% 2.58/0.98  
% 2.58/0.98  --sat_mode                              false
% 2.58/0.98  --sat_fm_restart_options                ""
% 2.58/0.98  --sat_gr_def                            false
% 2.58/0.98  --sat_epr_types                         true
% 2.58/0.98  --sat_non_cyclic_types                  false
% 2.58/0.98  --sat_finite_models                     false
% 2.58/0.98  --sat_fm_lemmas                         false
% 2.58/0.98  --sat_fm_prep                           false
% 2.58/0.98  --sat_fm_uc_incr                        true
% 2.58/0.98  --sat_out_model                         small
% 2.58/0.98  --sat_out_clauses                       false
% 2.58/0.98  
% 2.58/0.98  ------ QBF Options
% 2.58/0.98  
% 2.58/0.98  --qbf_mode                              false
% 2.58/0.98  --qbf_elim_univ                         false
% 2.58/0.98  --qbf_dom_inst                          none
% 2.58/0.98  --qbf_dom_pre_inst                      false
% 2.58/0.98  --qbf_sk_in                             false
% 2.58/0.98  --qbf_pred_elim                         true
% 2.58/0.98  --qbf_split                             512
% 2.58/0.98  
% 2.58/0.98  ------ BMC1 Options
% 2.58/0.98  
% 2.58/0.98  --bmc1_incremental                      false
% 2.58/0.98  --bmc1_axioms                           reachable_all
% 2.58/0.98  --bmc1_min_bound                        0
% 2.58/0.98  --bmc1_max_bound                        -1
% 2.58/0.98  --bmc1_max_bound_default                -1
% 2.58/0.98  --bmc1_symbol_reachability              true
% 2.58/0.98  --bmc1_property_lemmas                  false
% 2.58/0.98  --bmc1_k_induction                      false
% 2.58/0.98  --bmc1_non_equiv_states                 false
% 2.58/0.98  --bmc1_deadlock                         false
% 2.58/0.98  --bmc1_ucm                              false
% 2.58/0.98  --bmc1_add_unsat_core                   none
% 2.58/0.98  --bmc1_unsat_core_children              false
% 2.58/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.98  --bmc1_out_stat                         full
% 2.58/0.98  --bmc1_ground_init                      false
% 2.58/0.98  --bmc1_pre_inst_next_state              false
% 2.58/0.98  --bmc1_pre_inst_state                   false
% 2.58/0.98  --bmc1_pre_inst_reach_state             false
% 2.58/0.98  --bmc1_out_unsat_core                   false
% 2.58/0.98  --bmc1_aig_witness_out                  false
% 2.58/0.98  --bmc1_verbose                          false
% 2.58/0.98  --bmc1_dump_clauses_tptp                false
% 2.58/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.98  --bmc1_dump_file                        -
% 2.58/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.98  --bmc1_ucm_extend_mode                  1
% 2.58/0.98  --bmc1_ucm_init_mode                    2
% 2.58/0.98  --bmc1_ucm_cone_mode                    none
% 2.58/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.98  --bmc1_ucm_relax_model                  4
% 2.58/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.98  --bmc1_ucm_layered_model                none
% 2.58/0.98  --bmc1_ucm_max_lemma_size               10
% 2.58/0.98  
% 2.58/0.98  ------ AIG Options
% 2.58/0.98  
% 2.58/0.98  --aig_mode                              false
% 2.58/0.98  
% 2.58/0.98  ------ Instantiation Options
% 2.58/0.98  
% 2.58/0.98  --instantiation_flag                    true
% 2.58/0.98  --inst_sos_flag                         false
% 2.58/0.98  --inst_sos_phase                        true
% 2.58/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.98  --inst_lit_sel_side                     num_symb
% 2.58/0.98  --inst_solver_per_active                1400
% 2.58/0.98  --inst_solver_calls_frac                1.
% 2.58/0.98  --inst_passive_queue_type               priority_queues
% 2.58/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.98  --inst_passive_queues_freq              [25;2]
% 2.58/0.98  --inst_dismatching                      true
% 2.58/0.98  --inst_eager_unprocessed_to_passive     true
% 2.58/0.98  --inst_prop_sim_given                   true
% 2.58/0.98  --inst_prop_sim_new                     false
% 2.58/0.98  --inst_subs_new                         false
% 2.58/0.98  --inst_eq_res_simp                      false
% 2.58/0.98  --inst_subs_given                       false
% 2.58/0.98  --inst_orphan_elimination               true
% 2.58/0.98  --inst_learning_loop_flag               true
% 2.58/0.98  --inst_learning_start                   3000
% 2.58/0.98  --inst_learning_factor                  2
% 2.58/0.98  --inst_start_prop_sim_after_learn       3
% 2.58/0.98  --inst_sel_renew                        solver
% 2.58/0.98  --inst_lit_activity_flag                true
% 2.58/0.98  --inst_restr_to_given                   false
% 2.58/0.98  --inst_activity_threshold               500
% 2.58/0.98  --inst_out_proof                        true
% 2.58/0.98  
% 2.58/0.98  ------ Resolution Options
% 2.58/0.98  
% 2.58/0.98  --resolution_flag                       true
% 2.58/0.98  --res_lit_sel                           adaptive
% 2.58/0.98  --res_lit_sel_side                      none
% 2.58/0.98  --res_ordering                          kbo
% 2.58/0.98  --res_to_prop_solver                    active
% 2.58/0.98  --res_prop_simpl_new                    false
% 2.58/0.98  --res_prop_simpl_given                  true
% 2.58/0.98  --res_passive_queue_type                priority_queues
% 2.58/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.98  --res_passive_queues_freq               [15;5]
% 2.58/0.98  --res_forward_subs                      full
% 2.58/0.98  --res_backward_subs                     full
% 2.58/0.98  --res_forward_subs_resolution           true
% 2.58/0.98  --res_backward_subs_resolution          true
% 2.58/0.98  --res_orphan_elimination                true
% 2.58/0.98  --res_time_limit                        2.
% 2.58/0.98  --res_out_proof                         true
% 2.58/0.98  
% 2.58/0.98  ------ Superposition Options
% 2.58/0.98  
% 2.58/0.98  --superposition_flag                    true
% 2.58/0.98  --sup_passive_queue_type                priority_queues
% 2.58/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.98  --demod_completeness_check              fast
% 2.58/0.98  --demod_use_ground                      true
% 2.58/0.98  --sup_to_prop_solver                    passive
% 2.58/0.98  --sup_prop_simpl_new                    true
% 2.58/0.98  --sup_prop_simpl_given                  true
% 2.58/0.98  --sup_fun_splitting                     false
% 2.58/0.98  --sup_smt_interval                      50000
% 2.58/0.98  
% 2.58/0.98  ------ Superposition Simplification Setup
% 2.58/0.98  
% 2.58/0.98  --sup_indices_passive                   []
% 2.58/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.98  --sup_full_bw                           [BwDemod]
% 2.58/0.98  --sup_immed_triv                        [TrivRules]
% 2.58/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.98  --sup_immed_bw_main                     []
% 2.58/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.98  
% 2.58/0.98  ------ Combination Options
% 2.58/0.98  
% 2.58/0.98  --comb_res_mult                         3
% 2.58/0.98  --comb_sup_mult                         2
% 2.58/0.98  --comb_inst_mult                        10
% 2.58/0.98  
% 2.58/0.98  ------ Debug Options
% 2.58/0.98  
% 2.58/0.98  --dbg_backtrace                         false
% 2.58/0.98  --dbg_dump_prop_clauses                 false
% 2.58/0.98  --dbg_dump_prop_clauses_file            -
% 2.58/0.98  --dbg_out_stat                          false
% 2.58/0.98  ------ Parsing...
% 2.58/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/0.98  
% 2.58/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.58/0.98  
% 2.58/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/0.98  
% 2.58/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/0.98  ------ Proving...
% 2.58/0.98  ------ Problem Properties 
% 2.58/0.98  
% 2.58/0.98  
% 2.58/0.98  clauses                                 35
% 2.58/0.98  conjectures                             3
% 2.58/0.98  EPR                                     7
% 2.58/0.98  Horn                                    28
% 2.58/0.98  unary                                   4
% 2.58/0.98  binary                                  14
% 2.58/0.98  lits                                    89
% 2.58/0.98  lits eq                                 29
% 2.58/0.98  fd_pure                                 0
% 2.58/0.98  fd_pseudo                               0
% 2.58/0.98  fd_cond                                 2
% 2.58/0.98  fd_pseudo_cond                          2
% 2.58/0.98  AC symbols                              0
% 2.58/0.98  
% 2.58/0.98  ------ Schedule dynamic 5 is on 
% 2.58/0.98  
% 2.58/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/0.98  
% 2.58/0.98  
% 2.58/0.98  ------ 
% 2.58/0.98  Current options:
% 2.58/0.98  ------ 
% 2.58/0.98  
% 2.58/0.98  ------ Input Options
% 2.58/0.98  
% 2.58/0.98  --out_options                           all
% 2.58/0.98  --tptp_safe_out                         true
% 2.58/0.98  --problem_path                          ""
% 2.58/0.98  --include_path                          ""
% 2.58/0.98  --clausifier                            res/vclausify_rel
% 2.58/0.98  --clausifier_options                    --mode clausify
% 2.58/0.98  --stdin                                 false
% 2.58/0.98  --stats_out                             all
% 2.58/0.98  
% 2.58/0.98  ------ General Options
% 2.58/0.98  
% 2.58/0.98  --fof                                   false
% 2.58/0.98  --time_out_real                         305.
% 2.58/0.98  --time_out_virtual                      -1.
% 2.58/0.98  --symbol_type_check                     false
% 2.58/0.98  --clausify_out                          false
% 2.58/0.98  --sig_cnt_out                           false
% 2.58/0.98  --trig_cnt_out                          false
% 2.58/0.98  --trig_cnt_out_tolerance                1.
% 2.58/0.98  --trig_cnt_out_sk_spl                   false
% 2.58/0.98  --abstr_cl_out                          false
% 2.58/0.98  
% 2.58/0.98  ------ Global Options
% 2.58/0.98  
% 2.58/0.98  --schedule                              default
% 2.58/0.98  --add_important_lit                     false
% 2.58/0.98  --prop_solver_per_cl                    1000
% 2.58/0.98  --min_unsat_core                        false
% 2.58/0.98  --soft_assumptions                      false
% 2.58/0.98  --soft_lemma_size                       3
% 2.58/0.98  --prop_impl_unit_size                   0
% 2.58/0.98  --prop_impl_unit                        []
% 2.58/0.98  --share_sel_clauses                     true
% 2.58/0.98  --reset_solvers                         false
% 2.58/0.98  --bc_imp_inh                            [conj_cone]
% 2.58/0.98  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     none
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       false
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Simplification Setup
% 2.58/0.99  
% 2.58/0.99  --sup_indices_passive                   []
% 2.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_full_bw                           [BwDemod]
% 2.58/0.99  --sup_immed_triv                        [TrivRules]
% 2.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_immed_bw_main                     []
% 2.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  
% 2.58/0.99  ------ Combination Options
% 2.58/0.99  
% 2.58/0.99  --comb_res_mult                         3
% 2.58/0.99  --comb_sup_mult                         2
% 2.58/0.99  --comb_inst_mult                        10
% 2.58/0.99  
% 2.58/0.99  ------ Debug Options
% 2.58/0.99  
% 2.58/0.99  --dbg_backtrace                         false
% 2.58/0.99  --dbg_dump_prop_clauses                 false
% 2.58/0.99  --dbg_dump_prop_clauses_file            -
% 2.58/0.99  --dbg_out_stat                          false
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  ------ Proving...
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS status Theorem for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99   Resolution empty clause
% 2.58/0.99  
% 2.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  fof(f3,axiom,(
% 2.58/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f51,plain,(
% 2.58/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.99    inference(nnf_transformation,[],[f3])).
% 2.58/0.99  
% 2.58/0.99  fof(f52,plain,(
% 2.58/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.99    inference(flattening,[],[f51])).
% 2.58/0.99  
% 2.58/0.99  fof(f64,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.58/0.99    inference(cnf_transformation,[],[f52])).
% 2.58/0.99  
% 2.58/0.99  fof(f102,plain,(
% 2.58/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.58/0.99    inference(equality_resolution,[],[f64])).
% 2.58/0.99  
% 2.58/0.99  fof(f20,conjecture,(
% 2.58/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f21,negated_conjecture,(
% 2.58/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.58/0.99    inference(negated_conjecture,[],[f20])).
% 2.58/0.99  
% 2.58/0.99  fof(f43,plain,(
% 2.58/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.58/0.99    inference(ennf_transformation,[],[f21])).
% 2.58/0.99  
% 2.58/0.99  fof(f44,plain,(
% 2.58/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.58/0.99    inference(flattening,[],[f43])).
% 2.58/0.99  
% 2.58/0.99  fof(f58,plain,(
% 2.58/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f59,plain,(
% 2.58/0.99    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f58])).
% 2.58/0.99  
% 2.58/0.99  fof(f98,plain,(
% 2.58/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f14,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f34,plain,(
% 2.58/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(ennf_transformation,[],[f14])).
% 2.58/0.99  
% 2.58/0.99  fof(f83,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f34])).
% 2.58/0.99  
% 2.58/0.99  fof(f11,axiom,(
% 2.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f30,plain,(
% 2.58/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.58/0.99    inference(ennf_transformation,[],[f11])).
% 2.58/0.99  
% 2.58/0.99  fof(f55,plain,(
% 2.58/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.58/0.99    inference(nnf_transformation,[],[f30])).
% 2.58/0.99  
% 2.58/0.99  fof(f75,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f55])).
% 2.58/0.99  
% 2.58/0.99  fof(f13,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f33,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(ennf_transformation,[],[f13])).
% 2.58/0.99  
% 2.58/0.99  fof(f81,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f33])).
% 2.58/0.99  
% 2.58/0.99  fof(f4,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f23,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.58/0.99    inference(ennf_transformation,[],[f4])).
% 2.58/0.99  
% 2.58/0.99  fof(f24,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.58/0.99    inference(flattening,[],[f23])).
% 2.58/0.99  
% 2.58/0.99  fof(f66,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f99,plain,(
% 2.58/0.99    r1_tarski(sK3,sK4)),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f101,plain,(
% 2.58/0.99    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f96,plain,(
% 2.58/0.99    v1_funct_1(sK5)),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f19,axiom,(
% 2.58/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f41,plain,(
% 2.58/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.58/0.99    inference(ennf_transformation,[],[f19])).
% 2.58/0.99  
% 2.58/0.99  fof(f42,plain,(
% 2.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.58/0.99    inference(flattening,[],[f41])).
% 2.58/0.99  
% 2.58/0.99  fof(f94,plain,(
% 2.58/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f42])).
% 2.58/0.99  
% 2.58/0.99  fof(f17,axiom,(
% 2.58/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f37,plain,(
% 2.58/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.58/0.99    inference(ennf_transformation,[],[f17])).
% 2.58/0.99  
% 2.58/0.99  fof(f38,plain,(
% 2.58/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.58/0.99    inference(flattening,[],[f37])).
% 2.58/0.99  
% 2.58/0.99  fof(f86,plain,(
% 2.58/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f38])).
% 2.58/0.99  
% 2.58/0.99  fof(f18,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f39,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(ennf_transformation,[],[f18])).
% 2.58/0.99  
% 2.58/0.99  fof(f40,plain,(
% 2.58/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(flattening,[],[f39])).
% 2.58/0.99  
% 2.58/0.99  fof(f57,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(nnf_transformation,[],[f40])).
% 2.58/0.99  
% 2.58/0.99  fof(f87,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f57])).
% 2.58/0.99  
% 2.58/0.99  fof(f97,plain,(
% 2.58/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f16,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f36,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.99    inference(ennf_transformation,[],[f16])).
% 2.58/0.99  
% 2.58/0.99  fof(f85,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f36])).
% 2.58/0.99  
% 2.58/0.99  fof(f8,axiom,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f53,plain,(
% 2.58/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.58/0.99    inference(nnf_transformation,[],[f8])).
% 2.58/0.99  
% 2.58/0.99  fof(f70,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f53])).
% 2.58/0.99  
% 2.58/0.99  fof(f7,axiom,(
% 2.58/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f69,plain,(
% 2.58/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f7])).
% 2.58/0.99  
% 2.58/0.99  fof(f65,plain,(
% 2.58/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f52])).
% 2.58/0.99  
% 2.58/0.99  fof(f91,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f57])).
% 2.58/0.99  
% 2.58/0.99  fof(f109,plain,(
% 2.58/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.58/0.99    inference(equality_resolution,[],[f91])).
% 2.58/0.99  
% 2.58/0.99  fof(f100,plain,(
% 2.58/0.99    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 2.58/0.99    inference(cnf_transformation,[],[f59])).
% 2.58/0.99  
% 2.58/0.99  fof(f5,axiom,(
% 2.58/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f67,plain,(
% 2.58/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f5])).
% 2.58/0.99  
% 2.58/0.99  fof(f6,axiom,(
% 2.58/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f25,plain,(
% 2.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.58/0.99    inference(ennf_transformation,[],[f6])).
% 2.58/0.99  
% 2.58/0.99  fof(f26,plain,(
% 2.58/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.58/0.99    inference(flattening,[],[f25])).
% 2.58/0.99  
% 2.58/0.99  fof(f68,plain,(
% 2.58/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f26])).
% 2.58/0.99  
% 2.58/0.99  fof(f2,axiom,(
% 2.58/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f22,plain,(
% 2.58/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.58/0.99    inference(ennf_transformation,[],[f2])).
% 2.58/0.99  
% 2.58/0.99  fof(f49,plain,(
% 2.58/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f50,plain,(
% 2.58/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f49])).
% 2.58/0.99  
% 2.58/0.99  fof(f62,plain,(
% 2.58/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.58/0.99    inference(cnf_transformation,[],[f50])).
% 2.58/0.99  
% 2.58/0.99  fof(f12,axiom,(
% 2.58/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f31,plain,(
% 2.58/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f12])).
% 2.58/0.99  
% 2.58/0.99  fof(f32,plain,(
% 2.58/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.99    inference(flattening,[],[f31])).
% 2.58/0.99  
% 2.58/0.99  fof(f56,plain,(
% 2.58/0.99    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.99    inference(nnf_transformation,[],[f32])).
% 2.58/0.99  
% 2.58/0.99  fof(f77,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f56])).
% 2.58/0.99  
% 2.58/0.99  fof(f106,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.99    inference(equality_resolution,[],[f77])).
% 2.58/0.99  
% 2.58/0.99  fof(f1,axiom,(
% 2.58/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f45,plain,(
% 2.58/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.99    inference(nnf_transformation,[],[f1])).
% 2.58/0.99  
% 2.58/0.99  fof(f46,plain,(
% 2.58/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.99    inference(rectify,[],[f45])).
% 2.58/0.99  
% 2.58/0.99  fof(f47,plain,(
% 2.58/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f48,plain,(
% 2.58/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 2.58/0.99  
% 2.58/0.99  fof(f60,plain,(
% 2.58/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f48])).
% 2.58/0.99  
% 2.58/0.99  fof(f15,axiom,(
% 2.58/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f35,plain,(
% 2.58/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f15])).
% 2.58/0.99  
% 2.58/0.99  fof(f84,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f35])).
% 2.58/0.99  
% 2.58/0.99  fof(f95,plain,(
% 2.58/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f42])).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f102]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2311,plain,
% 2.58/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_39,negated_conjecture,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.58/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2300,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_22,plain,
% 2.58/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.58/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_16,plain,
% 2.58/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_557,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.58/0.99      | ~ v1_relat_1(X0) ),
% 2.58/0.99      inference(resolution,[status(thm)],[c_22,c_16]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_21,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_561,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_557,c_21]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_562,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_561]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2297,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4819,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2300,c_2297]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_6,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.58/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2310,plain,
% 2.58/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.58/0.99      | r1_tarski(X1,X2) != iProver_top
% 2.58/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5362,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 2.58/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_4819,c_2310]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_44,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_38,negated_conjecture,
% 2.58/0.99      ( r1_tarski(sK3,sK4) ),
% 2.58/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_45,plain,
% 2.58/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_36,negated_conjecture,
% 2.58/0.99      ( ~ v1_funct_2(sK5,sK2,sK4)
% 2.58/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | ~ v1_funct_1(sK5) ),
% 2.58/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_41,negated_conjecture,
% 2.58/0.99      ( v1_funct_1(sK5) ),
% 2.58/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_230,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | ~ v1_funct_2(sK5,sK2,sK4) ),
% 2.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_36,c_41]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_231,negated_conjecture,
% 2.58/0.99      ( ~ v1_funct_2(sK5,sK2,sK4)
% 2.58/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_230]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_34,plain,
% 2.58/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.58/0.99      | ~ v1_funct_1(X0)
% 2.58/0.99      | ~ v1_relat_1(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_578,plain,
% 2.58/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.58/0.99      | ~ v1_relat_1(X0)
% 2.58/0.99      | sK5 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_41]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_579,plain,
% 2.58/0.99      ( v1_funct_2(sK5,k1_relat_1(sK5),X0)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),X0)
% 2.58/0.99      | ~ v1_relat_1(sK5) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_578]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_956,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),X0)
% 2.58/0.99      | ~ v1_relat_1(sK5)
% 2.58/0.99      | k1_relat_1(sK5) != sK2
% 2.58/0.99      | sK4 != X0
% 2.58/0.99      | sK5 != sK5 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_231,c_579]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_957,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),sK4)
% 2.58/0.99      | ~ v1_relat_1(sK5)
% 2.58/0.99      | k1_relat_1(sK5) != sK2 ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_956]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_967,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | k1_relat_1(sK5) != sK2 ),
% 2.58/0.99      inference(forward_subsumption_resolution,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_957,c_21,c_562]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_970,plain,
% 2.58/0.99      ( k1_relat_1(sK5) != sK2
% 2.58/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2606,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK3) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_562]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2607,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_26,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 2.58/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2688,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.58/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),sK4) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2689,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.58/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_2688]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2651,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X2),X0)
% 2.58/0.99      | r1_tarski(k2_relat_1(X2),X1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3251,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),X0)
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),X1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_2651]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3515,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),X0)
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),sK3)
% 2.58/0.99      | ~ r1_tarski(sK3,X0) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_3251]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3516,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 2.58/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3515]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_32,plain,
% 2.58/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.58/0.99      | k1_xboole_0 = X2 ),
% 2.58/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_40,negated_conjecture,
% 2.58/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.58/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_906,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.58/0.99      | sK3 != X2
% 2.58/0.99      | sK2 != X1
% 2.58/0.99      | sK5 != X0
% 2.58/0.99      | k1_xboole_0 = X2 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_40]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_907,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.58/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.58/0.99      | k1_xboole_0 = sK3 ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_906]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_909,plain,
% 2.58/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_907,c_39]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_25,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2303,plain,
% 2.58/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.58/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3780,plain,
% 2.58/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2300,c_2303]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4126,plain,
% 2.58/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_909,c_3780]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_11,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_112,plain,
% 2.58/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.58/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_111,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.58/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_113,plain,
% 2.58/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.58/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_111]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_9,plain,
% 2.58/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_118,plain,
% 2.58/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_117,plain,
% 2.58/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_119,plain,
% 2.58/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_117]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.58/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_132,plain,
% 2.58/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1535,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2625,plain,
% 2.58/0.99      ( k1_relat_1(sK5) != X0 | k1_relat_1(sK5) = sK2 | sK2 != X0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2626,plain,
% 2.58/0.99      ( k1_relat_1(sK5) = sK2
% 2.58/0.99      | k1_relat_1(sK5) != k1_xboole_0
% 2.58/0.99      | sK2 != k1_xboole_0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_2625]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2621,plain,
% 2.58/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2773,plain,
% 2.58/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_2621]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1534,plain,( X0 = X0 ),theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2774,plain,
% 2.58/0.99      ( sK2 = sK2 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1534]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_28,plain,
% 2.58/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.58/0.99      | k1_xboole_0 = X1
% 2.58/0.99      | k1_xboole_0 = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_802,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.58/0.99      | sK3 != k1_xboole_0
% 2.58/0.99      | sK2 != X1
% 2.58/0.99      | sK5 != X0
% 2.58/0.99      | k1_xboole_0 = X0
% 2.58/0.99      | k1_xboole_0 = X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_40]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_803,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.58/0.99      | sK3 != k1_xboole_0
% 2.58/0.99      | k1_xboole_0 = sK2
% 2.58/0.99      | k1_xboole_0 = sK5 ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_802]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2291,plain,
% 2.58/0.99      ( sK3 != k1_xboole_0
% 2.58/0.99      | k1_xboole_0 = sK2
% 2.58/0.99      | k1_xboole_0 = sK5
% 2.58/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_37,negated_conjecture,
% 2.58/0.99      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 2.58/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2934,plain,
% 2.58/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2935,plain,
% 2.58/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_2934]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3006,plain,
% 2.58/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK2 ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_2291,c_37,c_112,c_118,c_132,c_2935]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1537,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.58/0.99      theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3357,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1)
% 2.58/0.99      | r1_tarski(sK3,k1_xboole_0)
% 2.58/0.99      | sK3 != X0
% 2.58/0.99      | k1_xboole_0 != X1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3358,plain,
% 2.58/0.99      ( sK3 != X0
% 2.58/0.99      | k1_xboole_0 != X1
% 2.58/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.58/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3357]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3360,plain,
% 2.58/0.99      ( sK3 != k1_xboole_0
% 2.58/0.99      | k1_xboole_0 != k1_xboole_0
% 2.58/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 2.58/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_3358]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_7,plain,
% 2.58/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_8,plain,
% 2.58/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_521,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_522,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_521]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3420,plain,
% 2.58/0.99      ( ~ r1_tarski(sK3,k1_xboole_0) | v1_xboole_0(sK3) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_522]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3421,plain,
% 2.58/0.99      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 2.58/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3420]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2,plain,
% 2.58/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2313,plain,
% 2.58/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_20,plain,
% 2.58/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.58/0.99      | ~ v1_funct_1(X1)
% 2.58/0.99      | ~ v1_relat_1(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_608,plain,
% 2.58/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.58/0.99      | ~ v1_relat_1(X1)
% 2.58/0.99      | sK5 != X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_609,plain,
% 2.58/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 2.58/0.99      | ~ v1_relat_1(sK5) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2295,plain,
% 2.58/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 2.58/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_610,plain,
% 2.58/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 2.58/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2586,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.58/0.99      | v1_relat_1(sK5) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2587,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.58/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_2586]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2628,plain,
% 2.58/0.99      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 2.58/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_2295,c_44,c_610,c_2587]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2629,plain,
% 2.58/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_2628]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1,plain,
% 2.58/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2314,plain,
% 2.58/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3214,plain,
% 2.58/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/0.99      | v1_xboole_0(sK5) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2629,c_2314]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3558,plain,
% 2.58/0.99      ( k1_relat_1(sK5) = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2313,c_3214]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_24,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/0.99      | ~ v1_xboole_0(X2)
% 2.58/0.99      | v1_xboole_0(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2304,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.58/0.99      | v1_xboole_0(X2) != iProver_top
% 2.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3948,plain,
% 2.58/0.99      ( v1_xboole_0(sK3) != iProver_top | v1_xboole_0(sK5) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2300,c_2304]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4457,plain,
% 2.58/0.99      ( k1_relat_1(sK5) = sK2 ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_4126,c_112,c_113,c_118,c_119,c_132,c_2626,c_2773,c_2774,
% 2.58/0.99                 c_3006,c_3360,c_3421,c_3558,c_3948]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_33,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.58/0.99      | ~ v1_funct_1(X0)
% 2.58/0.99      | ~ v1_relat_1(X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_593,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.58/0.99      | ~ v1_relat_1(X0)
% 2.58/0.99      | sK5 != X0 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_594,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 2.58/0.99      | ~ r1_tarski(k2_relat_1(sK5),X0)
% 2.58/0.99      | ~ v1_relat_1(sK5) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2296,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 2.58/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_595,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 2.58/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2637,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 2.58/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_2296,c_44,c_595,c_2587]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2638,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_2637]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4472,plain,
% 2.58/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_4457,c_2638]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5226,plain,
% 2.58/0.99      ( ~ r1_tarski(k2_relat_1(sK5),sK3)
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK4)
% 2.58/0.99      | ~ r1_tarski(sK3,sK4) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_3515]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5227,plain,
% 2.58/0.99      ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 2.58/0.99      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 2.58/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5226]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5746,plain,
% 2.58/0.99      ( r1_tarski(sK3,X0) != iProver_top ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_5362,c_44,c_45,c_112,c_113,c_118,c_119,c_132,c_970,c_2607,
% 2.58/0.99                 c_2626,c_2689,c_2773,c_2774,c_3006,c_3360,c_3421,c_3516,
% 2.58/0.99                 c_3558,c_3948,c_4126,c_4472,c_5227]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5753,plain,
% 2.58/0.99      ( $false ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_2311,c_5746]) ).
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  ------                               Statistics
% 2.58/0.99  
% 2.58/0.99  ------ General
% 2.58/0.99  
% 2.58/0.99  abstr_ref_over_cycles:                  0
% 2.58/0.99  abstr_ref_under_cycles:                 0
% 2.58/0.99  gc_basic_clause_elim:                   0
% 2.58/0.99  forced_gc_time:                         0
% 2.58/0.99  parsing_time:                           0.009
% 2.58/0.99  unif_index_cands_time:                  0.
% 2.58/0.99  unif_index_add_time:                    0.
% 2.58/0.99  orderings_time:                         0.
% 2.58/0.99  out_proof_time:                         0.009
% 2.58/0.99  total_time:                             0.166
% 2.58/0.99  num_of_symbols:                         55
% 2.58/0.99  num_of_terms:                           3362
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing
% 2.58/0.99  
% 2.58/0.99  num_of_splits:                          0
% 2.58/0.99  num_of_split_atoms:                     0
% 2.58/0.99  num_of_reused_defs:                     0
% 2.58/0.99  num_eq_ax_congr_red:                    26
% 2.58/0.99  num_of_sem_filtered_clauses:            1
% 2.58/0.99  num_of_subtypes:                        0
% 2.58/0.99  monotx_restored_types:                  0
% 2.58/0.99  sat_num_of_epr_types:                   0
% 2.58/0.99  sat_num_of_non_cyclic_types:            0
% 2.58/0.99  sat_guarded_non_collapsed_types:        0
% 2.58/0.99  num_pure_diseq_elim:                    0
% 2.58/0.99  simp_replaced_by:                       0
% 2.58/0.99  res_preprocessed:                       171
% 2.58/0.99  prep_upred:                             0
% 2.58/0.99  prep_unflattend:                        66
% 2.58/0.99  smt_new_axioms:                         0
% 2.58/0.99  pred_elim_cands:                        5
% 2.58/0.99  pred_elim:                              5
% 2.58/0.99  pred_elim_cl:                           4
% 2.58/0.99  pred_elim_cycles:                       8
% 2.58/0.99  merged_defs:                            8
% 2.58/0.99  merged_defs_ncl:                        0
% 2.58/0.99  bin_hyper_res:                          8
% 2.58/0.99  prep_cycles:                            4
% 2.58/0.99  pred_elim_time:                         0.014
% 2.58/0.99  splitting_time:                         0.
% 2.58/0.99  sem_filter_time:                        0.
% 2.58/0.99  monotx_time:                            0.
% 2.58/0.99  subtype_inf_time:                       0.
% 2.58/0.99  
% 2.58/0.99  ------ Problem properties
% 2.58/0.99  
% 2.58/0.99  clauses:                                35
% 2.58/0.99  conjectures:                            3
% 2.58/0.99  epr:                                    7
% 2.58/0.99  horn:                                   28
% 2.58/0.99  ground:                                 12
% 2.58/0.99  unary:                                  4
% 2.58/0.99  binary:                                 14
% 2.58/0.99  lits:                                   89
% 2.58/0.99  lits_eq:                                29
% 2.58/0.99  fd_pure:                                0
% 2.58/0.99  fd_pseudo:                              0
% 2.58/0.99  fd_cond:                                2
% 2.58/0.99  fd_pseudo_cond:                         2
% 2.58/0.99  ac_symbols:                             0
% 2.58/0.99  
% 2.58/0.99  ------ Propositional Solver
% 2.58/0.99  
% 2.58/0.99  prop_solver_calls:                      27
% 2.58/0.99  prop_fast_solver_calls:                 1176
% 2.58/0.99  smt_solver_calls:                       0
% 2.58/0.99  smt_fast_solver_calls:                  0
% 2.58/0.99  prop_num_of_clauses:                    1709
% 2.58/0.99  prop_preprocess_simplified:             7087
% 2.58/0.99  prop_fo_subsumed:                       16
% 2.58/0.99  prop_solver_time:                       0.
% 2.58/0.99  smt_solver_time:                        0.
% 2.58/0.99  smt_fast_solver_time:                   0.
% 2.58/0.99  prop_fast_solver_time:                  0.
% 2.58/0.99  prop_unsat_core_time:                   0.
% 2.58/0.99  
% 2.58/0.99  ------ QBF
% 2.58/0.99  
% 2.58/0.99  qbf_q_res:                              0
% 2.58/0.99  qbf_num_tautologies:                    0
% 2.58/0.99  qbf_prep_cycles:                        0
% 2.58/0.99  
% 2.58/0.99  ------ BMC1
% 2.58/0.99  
% 2.58/0.99  bmc1_current_bound:                     -1
% 2.58/0.99  bmc1_last_solved_bound:                 -1
% 2.58/0.99  bmc1_unsat_core_size:                   -1
% 2.58/0.99  bmc1_unsat_core_parents_size:           -1
% 2.58/0.99  bmc1_merge_next_fun:                    0
% 2.58/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation
% 2.58/0.99  
% 2.58/0.99  inst_num_of_clauses:                    490
% 2.58/0.99  inst_num_in_passive:                    192
% 2.58/0.99  inst_num_in_active:                     219
% 2.58/0.99  inst_num_in_unprocessed:                79
% 2.58/0.99  inst_num_of_loops:                      290
% 2.58/0.99  inst_num_of_learning_restarts:          0
% 2.58/0.99  inst_num_moves_active_passive:          69
% 2.58/0.99  inst_lit_activity:                      0
% 2.58/0.99  inst_lit_activity_moves:                0
% 2.58/0.99  inst_num_tautologies:                   0
% 2.58/0.99  inst_num_prop_implied:                  0
% 2.58/0.99  inst_num_existing_simplified:           0
% 2.58/0.99  inst_num_eq_res_simplified:             0
% 2.58/0.99  inst_num_child_elim:                    0
% 2.58/0.99  inst_num_of_dismatching_blockings:      170
% 2.58/0.99  inst_num_of_non_proper_insts:           564
% 2.58/0.99  inst_num_of_duplicates:                 0
% 2.58/0.99  inst_inst_num_from_inst_to_res:         0
% 2.58/0.99  inst_dismatching_checking_time:         0.
% 2.58/0.99  
% 2.58/0.99  ------ Resolution
% 2.58/0.99  
% 2.58/0.99  res_num_of_clauses:                     0
% 2.58/0.99  res_num_in_passive:                     0
% 2.58/0.99  res_num_in_active:                      0
% 2.58/0.99  res_num_of_loops:                       175
% 2.58/0.99  res_forward_subset_subsumed:            24
% 2.58/0.99  res_backward_subset_subsumed:           0
% 2.58/0.99  res_forward_subsumed:                   0
% 2.58/0.99  res_backward_subsumed:                  0
% 2.58/0.99  res_forward_subsumption_resolution:     5
% 2.58/0.99  res_backward_subsumption_resolution:    0
% 2.58/0.99  res_clause_to_clause_subsumption:       315
% 2.58/0.99  res_orphan_elimination:                 0
% 2.58/0.99  res_tautology_del:                      57
% 2.58/0.99  res_num_eq_res_simplified:              1
% 2.58/0.99  res_num_sel_changes:                    0
% 2.58/0.99  res_moves_from_active_to_pass:          0
% 2.58/0.99  
% 2.58/0.99  ------ Superposition
% 2.58/0.99  
% 2.58/0.99  sup_time_total:                         0.
% 2.58/0.99  sup_time_generating:                    0.
% 2.58/0.99  sup_time_sim_full:                      0.
% 2.58/0.99  sup_time_sim_immed:                     0.
% 2.58/0.99  
% 2.58/0.99  sup_num_of_clauses:                     74
% 2.58/0.99  sup_num_in_active:                      42
% 2.58/0.99  sup_num_in_passive:                     32
% 2.58/0.99  sup_num_of_loops:                       56
% 2.58/0.99  sup_fw_superposition:                   45
% 2.58/0.99  sup_bw_superposition:                   7
% 2.58/0.99  sup_immediate_simplified:               3
% 2.58/0.99  sup_given_eliminated:                   0
% 2.58/0.99  comparisons_done:                       0
% 2.58/0.99  comparisons_avoided:                    1
% 2.58/0.99  
% 2.58/0.99  ------ Simplifications
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  sim_fw_subset_subsumed:                 0
% 2.58/0.99  sim_bw_subset_subsumed:                 1
% 2.58/0.99  sim_fw_subsumed:                        2
% 2.58/0.99  sim_bw_subsumed:                        1
% 2.58/0.99  sim_fw_subsumption_res:                 0
% 2.58/0.99  sim_bw_subsumption_res:                 0
% 2.58/0.99  sim_tautology_del:                      1
% 2.58/0.99  sim_eq_tautology_del:                   2
% 2.58/0.99  sim_eq_res_simp:                        1
% 2.58/0.99  sim_fw_demodulated:                     0
% 2.58/0.99  sim_bw_demodulated:                     14
% 2.58/0.99  sim_light_normalised:                   0
% 2.58/0.99  sim_joinable_taut:                      0
% 2.58/0.99  sim_joinable_simp:                      0
% 2.58/0.99  sim_ac_normalised:                      0
% 2.58/0.99  sim_smt_subsumption:                    0
% 2.58/0.99  
%------------------------------------------------------------------------------
