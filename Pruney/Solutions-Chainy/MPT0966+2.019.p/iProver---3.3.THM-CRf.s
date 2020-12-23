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

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  250 (4735 expanded)
%              Number of clauses        :  163 (1934 expanded)
%              Number of leaves         :   25 ( 879 expanded)
%              Depth                    :   28
%              Number of atoms          :  715 (21781 expanded)
%              Number of equality atoms :  385 (7303 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f49])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f40])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_570,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_572,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_34])).

cnf(c_1472,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1477,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3750,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1472,c_1477])).

cnf(c_3855,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_572,c_3750])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_1469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1835,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1469])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1476,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3299,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1472,c_1476])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1473,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3408,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3299,c_1473])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3748,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_1477])).

cnf(c_27592,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_3748])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2890,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1482])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_267])).

cnf(c_1471,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_3328,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2890,c_1471])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1480,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3522,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3328,c_1480])).

cnf(c_29106,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27592,c_3522])).

cnf(c_29107,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29106])).

cnf(c_29117,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_29107])).

cnf(c_29166,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29117,c_3522])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_191,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_36])).

cnf(c_192,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_192])).

cnf(c_557,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_1464,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_29169,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29166,c_1464])).

cnf(c_2085,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2086,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2085])).

cnf(c_29231,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29169,c_1835,c_2086,c_3408,c_3522])).

cnf(c_29232,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_29231])).

cnf(c_29235,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3855,c_29232])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29247,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29235,c_32])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1707,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_860,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1989,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2762,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_267])).

cnf(c_440,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_327])).

cnf(c_441,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1470,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2295,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1470])).

cnf(c_3407,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3299,c_2295])).

cnf(c_3415,plain,
    ( ~ v1_xboole_0(sK3)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3407])).

cnf(c_3523,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3522])).

cnf(c_862,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4314,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_4316,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4314])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5430,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6965,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3006,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1469])).

cnf(c_7399,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3006])).

cnf(c_7440,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3855,c_7399])).

cnf(c_1796,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1920,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1983,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1984,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_1986,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1787,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1999,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_2773,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_2775,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK1
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_2774,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2777,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2774])).

cnf(c_2808,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2811,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1481,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3922,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3855,c_1481])).

cnf(c_119,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_508,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1467,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1592,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1467,c_7])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_861,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1725,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1795,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_1954,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1955,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_2081,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1592,c_32,c_103,c_104,c_1795,c_1796,c_1955])).

cnf(c_2699,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_2700,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2699])).

cnf(c_2702,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_4098,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3922,c_119,c_2081,c_2702])).

cnf(c_4100,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4098])).

cnf(c_6912,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_6914,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6912])).

cnf(c_7763,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7440,c_0,c_1796,c_1920,c_1986,c_2775,c_2777,c_2811,c_4100,c_6914])).

cnf(c_7764,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7763])).

cnf(c_7765,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7764])).

cnf(c_2495,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_4950,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2495])).

cnf(c_10240,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK4)
    | X0 != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_10242,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_10240])).

cnf(c_29340,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29247,c_0,c_1707,c_1989,c_2762,c_3415,c_3523,c_4316,c_5430,c_6965,c_7765,c_10242])).

cnf(c_29344,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_29340,c_29166])).

cnf(c_29469,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_29340,c_3750])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_544,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1465,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_1585,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1465,c_8])).

cnf(c_29478,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29340,c_1585])).

cnf(c_29495,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29478])).

cnf(c_29481,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29340,c_1472])).

cnf(c_29484,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29481,c_8])).

cnf(c_29498,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29495,c_29484])).

cnf(c_29528,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29469,c_29498])).

cnf(c_29958,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29344,c_29528])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_192])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_1466,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1615,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1466,c_8])).

cnf(c_29477,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29340,c_1615])).

cnf(c_29500,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29477])).

cnf(c_29504,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29500,c_29484])).

cnf(c_29505,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29504,c_8])).

cnf(c_29960,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29958,c_29505])).

cnf(c_29962,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29960])).

cnf(c_29964,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29962,c_29484])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.07/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.07/1.49  
% 7.07/1.49  ------  iProver source info
% 7.07/1.49  
% 7.07/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.07/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.07/1.49  git: non_committed_changes: false
% 7.07/1.49  git: last_make_outside_of_git: false
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     num_symb
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       true
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  ------ Parsing...
% 7.07/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.07/1.49  ------ Proving...
% 7.07/1.49  ------ Problem Properties 
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  clauses                                 31
% 7.07/1.49  conjectures                             3
% 7.07/1.49  EPR                                     8
% 7.07/1.49  Horn                                    28
% 7.07/1.49  unary                                   9
% 7.07/1.49  binary                                  9
% 7.07/1.49  lits                                    71
% 7.07/1.49  lits eq                                 31
% 7.07/1.49  fd_pure                                 0
% 7.07/1.49  fd_pseudo                               0
% 7.07/1.49  fd_cond                                 5
% 7.07/1.49  fd_pseudo_cond                          1
% 7.07/1.49  AC symbols                              0
% 7.07/1.49  
% 7.07/1.49  ------ Schedule dynamic 5 is on 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  Current options:
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     none
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       false
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ Proving...
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  % SZS status Theorem for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49   Resolution empty clause
% 7.07/1.49  
% 7.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  fof(f19,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f36,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(ennf_transformation,[],[f19])).
% 7.07/1.49  
% 7.07/1.49  fof(f37,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(flattening,[],[f36])).
% 7.07/1.49  
% 7.07/1.49  fof(f48,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(nnf_transformation,[],[f37])).
% 7.07/1.49  
% 7.07/1.49  fof(f76,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f20,conjecture,(
% 7.07/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f21,negated_conjecture,(
% 7.07/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.07/1.49    inference(negated_conjecture,[],[f20])).
% 7.07/1.49  
% 7.07/1.49  fof(f38,plain,(
% 7.07/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.07/1.49    inference(ennf_transformation,[],[f21])).
% 7.07/1.49  
% 7.07/1.49  fof(f39,plain,(
% 7.07/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.07/1.49    inference(flattening,[],[f38])).
% 7.07/1.49  
% 7.07/1.49  fof(f49,plain,(
% 7.07/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f50,plain,(
% 7.07/1.49    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f49])).
% 7.07/1.49  
% 7.07/1.49  fof(f83,plain,(
% 7.07/1.49    v1_funct_2(sK4,sK1,sK2)),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f84,plain,(
% 7.07/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f15,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f32,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(ennf_transformation,[],[f15])).
% 7.07/1.49  
% 7.07/1.49  fof(f72,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f32])).
% 7.07/1.49  
% 7.07/1.49  fof(f14,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f22,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.07/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.07/1.49  
% 7.07/1.49  fof(f31,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(ennf_transformation,[],[f22])).
% 7.07/1.49  
% 7.07/1.49  fof(f71,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f10,axiom,(
% 7.07/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f27,plain,(
% 7.07/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.07/1.49    inference(ennf_transformation,[],[f10])).
% 7.07/1.49  
% 7.07/1.49  fof(f47,plain,(
% 7.07/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.07/1.49    inference(nnf_transformation,[],[f27])).
% 7.07/1.49  
% 7.07/1.49  fof(f65,plain,(
% 7.07/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f47])).
% 7.07/1.49  
% 7.07/1.49  fof(f16,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f33,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(ennf_transformation,[],[f16])).
% 7.07/1.49  
% 7.07/1.49  fof(f73,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f33])).
% 7.07/1.49  
% 7.07/1.49  fof(f85,plain,(
% 7.07/1.49    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f17,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f34,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.07/1.49    inference(ennf_transformation,[],[f17])).
% 7.07/1.49  
% 7.07/1.49  fof(f35,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.07/1.49    inference(flattening,[],[f34])).
% 7.07/1.49  
% 7.07/1.49  fof(f74,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f35])).
% 7.07/1.49  
% 7.07/1.49  fof(f7,axiom,(
% 7.07/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f46,plain,(
% 7.07/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.07/1.49    inference(nnf_transformation,[],[f7])).
% 7.07/1.49  
% 7.07/1.49  fof(f61,plain,(
% 7.07/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f46])).
% 7.07/1.49  
% 7.07/1.49  fof(f9,axiom,(
% 7.07/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f26,plain,(
% 7.07/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f9])).
% 7.07/1.49  
% 7.07/1.49  fof(f64,plain,(
% 7.07/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f26])).
% 7.07/1.49  
% 7.07/1.49  fof(f62,plain,(
% 7.07/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f46])).
% 7.07/1.49  
% 7.07/1.49  fof(f12,axiom,(
% 7.07/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f68,plain,(
% 7.07/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f12])).
% 7.07/1.49  
% 7.07/1.49  fof(f78,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f87,plain,(
% 7.07/1.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f82,plain,(
% 7.07/1.49    v1_funct_1(sK4)),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f86,plain,(
% 7.07/1.49    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 7.07/1.49    inference(cnf_transformation,[],[f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f1,axiom,(
% 7.07/1.49    v1_xboole_0(k1_xboole_0)),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f51,plain,(
% 7.07/1.49    v1_xboole_0(k1_xboole_0)),
% 7.07/1.49    inference(cnf_transformation,[],[f1])).
% 7.07/1.49  
% 7.07/1.49  fof(f4,axiom,(
% 7.07/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f42,plain,(
% 7.07/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.49    inference(nnf_transformation,[],[f4])).
% 7.07/1.49  
% 7.07/1.49  fof(f43,plain,(
% 7.07/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.49    inference(flattening,[],[f42])).
% 7.07/1.49  
% 7.07/1.49  fof(f56,plain,(
% 7.07/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f43])).
% 7.07/1.49  
% 7.07/1.49  fof(f54,plain,(
% 7.07/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.07/1.49    inference(cnf_transformation,[],[f43])).
% 7.07/1.49  
% 7.07/1.49  fof(f89,plain,(
% 7.07/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.07/1.49    inference(equality_resolution,[],[f54])).
% 7.07/1.49  
% 7.07/1.49  fof(f3,axiom,(
% 7.07/1.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f24,plain,(
% 7.07/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.07/1.49    inference(ennf_transformation,[],[f3])).
% 7.07/1.49  
% 7.07/1.49  fof(f40,plain,(
% 7.07/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f41,plain,(
% 7.07/1.49    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f40])).
% 7.07/1.49  
% 7.07/1.49  fof(f53,plain,(
% 7.07/1.49    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 7.07/1.49    inference(cnf_transformation,[],[f41])).
% 7.07/1.49  
% 7.07/1.49  fof(f8,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f25,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.07/1.49    inference(ennf_transformation,[],[f8])).
% 7.07/1.49  
% 7.07/1.49  fof(f63,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f25])).
% 7.07/1.49  
% 7.07/1.49  fof(f13,axiom,(
% 7.07/1.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f29,plain,(
% 7.07/1.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f13])).
% 7.07/1.49  
% 7.07/1.49  fof(f30,plain,(
% 7.07/1.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.07/1.49    inference(flattening,[],[f29])).
% 7.07/1.49  
% 7.07/1.49  fof(f70,plain,(
% 7.07/1.49    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f30])).
% 7.07/1.49  
% 7.07/1.49  fof(f5,axiom,(
% 7.07/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f57,plain,(
% 7.07/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f5])).
% 7.07/1.49  
% 7.07/1.49  fof(f6,axiom,(
% 7.07/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f44,plain,(
% 7.07/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.07/1.49    inference(nnf_transformation,[],[f6])).
% 7.07/1.49  
% 7.07/1.49  fof(f45,plain,(
% 7.07/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.07/1.49    inference(flattening,[],[f44])).
% 7.07/1.49  
% 7.07/1.49  fof(f59,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.07/1.49    inference(cnf_transformation,[],[f45])).
% 7.07/1.49  
% 7.07/1.49  fof(f91,plain,(
% 7.07/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.07/1.49    inference(equality_resolution,[],[f59])).
% 7.07/1.49  
% 7.07/1.49  fof(f2,axiom,(
% 7.07/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f23,plain,(
% 7.07/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f2])).
% 7.07/1.49  
% 7.07/1.49  fof(f52,plain,(
% 7.07/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f23])).
% 7.07/1.49  
% 7.07/1.49  fof(f11,axiom,(
% 7.07/1.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 7.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f28,plain,(
% 7.07/1.49    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f11])).
% 7.07/1.49  
% 7.07/1.49  fof(f67,plain,(
% 7.07/1.49    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f28])).
% 7.07/1.49  
% 7.07/1.49  fof(f80,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f94,plain,(
% 7.07/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.07/1.49    inference(equality_resolution,[],[f80])).
% 7.07/1.49  
% 7.07/1.49  fof(f60,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.07/1.49    inference(cnf_transformation,[],[f45])).
% 7.07/1.49  
% 7.07/1.49  fof(f90,plain,(
% 7.07/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.07/1.49    inference(equality_resolution,[],[f60])).
% 7.07/1.49  
% 7.07/1.49  fof(f58,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f45])).
% 7.07/1.49  
% 7.07/1.49  fof(f77,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f96,plain,(
% 7.07/1.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.07/1.49    inference(equality_resolution,[],[f77])).
% 7.07/1.49  
% 7.07/1.49  fof(f79,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f95,plain,(
% 7.07/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.07/1.49    inference(equality_resolution,[],[f79])).
% 7.07/1.49  
% 7.07/1.49  cnf(c_30,plain,
% 7.07/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.07/1.49      | k1_xboole_0 = X2 ),
% 7.07/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_35,negated_conjecture,
% 7.07/1.49      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.07/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_569,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.07/1.49      | sK2 != X2
% 7.07/1.49      | sK1 != X1
% 7.07/1.49      | sK4 != X0
% 7.07/1.49      | k1_xboole_0 = X2 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_570,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.07/1.49      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.07/1.49      | k1_xboole_0 = sK2 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_569]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_34,negated_conjecture,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.07/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_572,plain,
% 7.07/1.49      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 7.07/1.49      inference(global_propositional_subsumption,[status(thm)],[c_570,c_34]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1472,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_21,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1477,plain,
% 7.07/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.07/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3750,plain,
% 7.07/1.49      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1472,c_1477]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3855,plain,
% 7.07/1.49      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_572,c_3750]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_20,plain,
% 7.07/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.07/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_15,plain,
% 7.07/1.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_457,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.07/1.49      | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1469,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.07/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1835,plain,
% 7.07/1.49      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 7.07/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1472,c_1469]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_22,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1476,plain,
% 7.07/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.07/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3299,plain,
% 7.07/1.49      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1472,c_1476]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_33,negated_conjecture,
% 7.07/1.49      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 7.07/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1473,plain,
% 7.07/1.49      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3408,plain,
% 7.07/1.49      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_3299,c_1473]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_23,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.07/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.07/1.49      | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1475,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.07/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.07/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3748,plain,
% 7.07/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.07/1.49      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.07/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1475,c_1477]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_27592,plain,
% 7.07/1.49      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 7.07/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.07/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3408,c_3748]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_11,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1482,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.07/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2890,plain,
% 7.07/1.49      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1472,c_1482]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_13,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_10,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_266,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.07/1.49      inference(prop_impl,[status(thm)],[c_10]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_267,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_266]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_328,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.07/1.49      inference(bin_hyper_res,[status(thm)],[c_13,c_267]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1471,plain,
% 7.07/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.07/1.49      | v1_relat_1(X1) != iProver_top
% 7.07/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3328,plain,
% 7.07/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.07/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_2890,c_1471]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_17,plain,
% 7.07/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1480,plain,
% 7.07/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3522,plain,
% 7.07/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.07/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_3328,c_1480]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29106,plain,
% 7.07/1.49      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.07/1.49      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_27592,c_3522]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29107,plain,
% 7.07/1.49      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 7.07/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_29106]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29117,plain,
% 7.07/1.49      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
% 7.07/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1835,c_29107]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29166,plain,
% 7.07/1.49      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_29117,c_3522]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_28,plain,
% 7.07/1.49      ( v1_funct_2(X0,X1,X2)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.07/1.49      | k1_xboole_0 = X2 ),
% 7.07/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_31,negated_conjecture,
% 7.07/1.49      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.07/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | ~ v1_funct_1(sK4) ),
% 7.07/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_36,negated_conjecture,
% 7.07/1.49      ( v1_funct_1(sK4) ),
% 7.07/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_191,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 7.07/1.49      inference(global_propositional_subsumption,[status(thm)],[c_31,c_36]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_192,negated_conjecture,
% 7.07/1.49      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.07/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_191]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_556,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.07/1.49      | sK3 != X2
% 7.07/1.49      | sK1 != X1
% 7.07/1.49      | sK4 != X0
% 7.07/1.49      | k1_xboole_0 = X2 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_192]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_557,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | k1_relset_1(sK1,sK3,sK4) != sK1
% 7.07/1.49      | k1_xboole_0 = sK3 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_556]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1464,plain,
% 7.07/1.49      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 7.07/1.49      | k1_xboole_0 = sK3
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29169,plain,
% 7.07/1.49      ( k1_relat_1(sK4) != sK1
% 7.07/1.49      | sK3 = k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29166,c_1464]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2085,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 7.07/1.49      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 7.07/1.49      | ~ v1_relat_1(sK4) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2086,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 7.07/1.49      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 7.07/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_2085]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29231,plain,
% 7.07/1.49      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) != sK1 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_29169,c_1835,c_2086,c_3408,c_3522]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29232,plain,
% 7.07/1.49      ( k1_relat_1(sK4) != sK1 | sK3 = k1_xboole_0 ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_29231]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29235,plain,
% 7.07/1.49      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3855,c_29232]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_32,negated_conjecture,
% 7.07/1.49      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 7.07/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29247,plain,
% 7.07/1.49      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_29235,c_32]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_0,plain,
% 7.07/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.07/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1707,plain,
% 7.07/1.49      ( ~ r1_tarski(sK1,k1_xboole_0)
% 7.07/1.49      | ~ r1_tarski(k1_xboole_0,sK1)
% 7.07/1.49      | sK1 = k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_860,plain,( X0 = X0 ),theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1989,plain,
% 7.07/1.49      ( sK4 = sK4 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_860]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f89]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2762,plain,
% 7.07/1.49      ( r1_tarski(sK4,sK4) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2,plain,
% 7.07/1.49      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_12,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.07/1.49      | ~ r2_hidden(X2,X0)
% 7.07/1.49      | ~ v1_xboole_0(X1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_327,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 7.07/1.49      inference(bin_hyper_res,[status(thm)],[c_12,c_267]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_440,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1)
% 7.07/1.49      | ~ v1_xboole_0(X1)
% 7.07/1.49      | X0 != X2
% 7.07/1.49      | sK0(X2) != X3
% 7.07/1.49      | k1_xboole_0 = X2 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_327]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_441,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_440]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1470,plain,
% 7.07/1.49      ( k1_xboole_0 = X0
% 7.07/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.07/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2295,plain,
% 7.07/1.49      ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | v1_xboole_0(sK3) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1473,c_1470]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3407,plain,
% 7.07/1.49      ( k2_relat_1(sK4) = k1_xboole_0 | v1_xboole_0(sK3) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_3299,c_2295]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3415,plain,
% 7.07/1.49      ( ~ v1_xboole_0(sK3) | k2_relat_1(sK4) = k1_xboole_0 ),
% 7.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3407]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3523,plain,
% 7.07/1.49      ( v1_relat_1(sK4) ),
% 7.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3522]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_862,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.07/1.49      theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4314,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_862]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4316,plain,
% 7.07/1.49      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_4314]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_18,plain,
% 7.07/1.49      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5430,plain,
% 7.07/1.49      ( ~ v1_relat_1(sK4)
% 7.07/1.49      | k2_relat_1(sK4) != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 = sK4 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6,plain,
% 7.07/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6965,plain,
% 7.07/1.49      ( r1_tarski(k1_xboole_0,sK1) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_8,plain,
% 7.07/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1483,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.07/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3006,plain,
% 7.07/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.07/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_1483,c_1469]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7399,plain,
% 7.07/1.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 7.07/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_8,c_3006]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7440,plain,
% 7.07/1.49      ( sK2 = k1_xboole_0
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.07/1.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 7.07/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3855,c_7399]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1796,plain,
% 7.07/1.49      ( sK1 = sK1 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_860]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1920,plain,
% 7.07/1.49      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1983,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1984,plain,
% 7.07/1.49      ( sK4 = X0
% 7.07/1.49      | r1_tarski(X0,sK4) != iProver_top
% 7.07/1.49      | r1_tarski(sK4,X0) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1986,plain,
% 7.07/1.49      ( sK4 = k1_xboole_0
% 7.07/1.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 7.07/1.49      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1984]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_863,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.07/1.49      theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1787,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1)
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.07/1.49      | sK1 != X0
% 7.07/1.49      | k1_xboole_0 != X1 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_863]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1999,plain,
% 7.07/1.49      ( ~ r1_tarski(sK1,X0)
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.07/1.49      | sK1 != sK1
% 7.07/1.49      | k1_xboole_0 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1787]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2773,plain,
% 7.07/1.49      ( ~ r1_tarski(sK1,sK1)
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.07/1.49      | sK1 != sK1
% 7.07/1.49      | k1_xboole_0 != sK1 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1999]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2775,plain,
% 7.07/1.49      ( sK1 != sK1
% 7.07/1.49      | k1_xboole_0 != sK1
% 7.07/1.49      | r1_tarski(sK1,sK1) != iProver_top
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2774,plain,
% 7.07/1.49      ( r1_tarski(sK1,sK1) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2777,plain,
% 7.07/1.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_2774]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2808,plain,
% 7.07/1.49      ( r1_tarski(k1_xboole_0,sK4) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2811,plain,
% 7.07/1.49      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_16,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1481,plain,
% 7.07/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.07/1.49      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3922,plain,
% 7.07/1.49      ( sK2 = k1_xboole_0
% 7.07/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.07/1.49      | v1_xboole_0(sK4) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3855,c_1481]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_119,plain,
% 7.07/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_26,plain,
% 7.07/1.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.07/1.49      | k1_xboole_0 = X1
% 7.07/1.49      | k1_xboole_0 = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_507,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.07/1.49      | sK2 != k1_xboole_0
% 7.07/1.49      | sK1 != X1
% 7.07/1.49      | sK4 != X0
% 7.07/1.49      | k1_xboole_0 = X0
% 7.07/1.49      | k1_xboole_0 = X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_508,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.07/1.49      | sK2 != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 = sK1
% 7.07/1.49      | k1_xboole_0 = sK4 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_507]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1467,plain,
% 7.07/1.49      ( sK2 != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 = sK1
% 7.07/1.49      | k1_xboole_0 = sK4
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7,plain,
% 7.07/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1592,plain,
% 7.07/1.49      ( sK2 != k1_xboole_0
% 7.07/1.49      | sK1 = k1_xboole_0
% 7.07/1.49      | sK4 = k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_1467,c_7]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_9,plain,
% 7.07/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 = X0
% 7.07/1.49      | k1_xboole_0 = X1 ),
% 7.07/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_103,plain,
% 7.07/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_104,plain,
% 7.07/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_861,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1725,plain,
% 7.07/1.49      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_861]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1795,plain,
% 7.07/1.49      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1725]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1954,plain,
% 7.07/1.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_861]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1955,plain,
% 7.07/1.49      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2081,plain,
% 7.07/1.49      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_1592,c_32,c_103,c_104,c_1795,c_1796,c_1955]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2699,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_862]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2700,plain,
% 7.07/1.49      ( sK1 != X0
% 7.07/1.49      | v1_xboole_0(X0) != iProver_top
% 7.07/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_2699]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2702,plain,
% 7.07/1.49      ( sK1 != k1_xboole_0
% 7.07/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.07/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_2700]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4098,plain,
% 7.07/1.49      ( v1_xboole_0(sK1) = iProver_top | v1_xboole_0(sK4) != iProver_top ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_3922,c_119,c_2081,c_2702]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4100,plain,
% 7.07/1.49      ( v1_xboole_0(sK1) | ~ v1_xboole_0(sK4) ),
% 7.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4098]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6912,plain,
% 7.07/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_862]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6914,plain,
% 7.07/1.49      ( v1_xboole_0(sK4) | ~ v1_xboole_0(k1_xboole_0) | sK4 != k1_xboole_0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_6912]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7763,plain,
% 7.07/1.49      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 7.07/1.49      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_7440,c_0,c_1796,c_1920,c_1986,c_2775,c_2777,c_2811,c_4100,
% 7.07/1.49                 c_6914]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7764,plain,
% 7.07/1.49      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.07/1.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_7763]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7765,plain,
% 7.07/1.49      ( r1_tarski(sK1,k1_xboole_0) | ~ r1_tarski(sK4,k1_xboole_0) ),
% 7.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_7764]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2495,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_863]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4950,plain,
% 7.07/1.49      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_2495]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_10240,plain,
% 7.07/1.49      ( r1_tarski(sK4,X0) | ~ r1_tarski(sK4,sK4) | X0 != sK4 | sK4 != sK4 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_4950]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_10242,plain,
% 7.07/1.49      ( ~ r1_tarski(sK4,sK4)
% 7.07/1.49      | r1_tarski(sK4,k1_xboole_0)
% 7.07/1.49      | sK4 != sK4
% 7.07/1.49      | k1_xboole_0 != sK4 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_10240]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29340,plain,
% 7.07/1.49      ( sK1 = k1_xboole_0 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_29247,c_0,c_1707,c_1989,c_2762,c_3415,c_3523,c_4316,
% 7.07/1.49                 c_5430,c_6965,c_7765,c_10242]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29344,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29340,c_29166]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29469,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29340,c_3750]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29,plain,
% 7.07/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_543,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.07/1.49      | sK2 != X1
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | sK4 != X0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_544,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_543]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1465,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1585,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_1465,c_8]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29478,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | k1_xboole_0 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29340,c_1585]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29495,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(equality_resolution_simp,[status(thm)],[c_29478]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29481,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29340,c_1472]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29484,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29481,c_8]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29498,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
% 7.07/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_29495,c_29484]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29528,plain,
% 7.07/1.49      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.07/1.49      inference(light_normalisation,[status(thm)],[c_29469,c_29498]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29958,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
% 7.07/1.49      inference(light_normalisation,[status(thm)],[c_29344,c_29528]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_27,plain,
% 7.07/1.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_527,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.07/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.07/1.49      | sK3 != X1
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | sK4 != X0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_192]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_528,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.07/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 7.07/1.49      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_527]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1466,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1615,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | sK1 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_1466,c_8]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29477,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | k1_xboole_0 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29340,c_1615]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29500,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(equality_resolution_simp,[status(thm)],[c_29477]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29504,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 7.07/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_29500,c_29484]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29505,plain,
% 7.07/1.49      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29504,c_8]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29960,plain,
% 7.07/1.49      ( k1_xboole_0 != k1_xboole_0
% 7.07/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_29958,c_29505]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29962,plain,
% 7.07/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.07/1.49      inference(equality_resolution_simp,[status(thm)],[c_29960]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29964,plain,
% 7.07/1.49      ( $false ),
% 7.07/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_29962,c_29484]) ).
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  ------                               Statistics
% 7.07/1.49  
% 7.07/1.49  ------ General
% 7.07/1.49  
% 7.07/1.49  abstr_ref_over_cycles:                  0
% 7.07/1.49  abstr_ref_under_cycles:                 0
% 7.07/1.49  gc_basic_clause_elim:                   0
% 7.07/1.49  forced_gc_time:                         0
% 7.07/1.49  parsing_time:                           0.016
% 7.07/1.49  unif_index_cands_time:                  0.
% 7.07/1.49  unif_index_add_time:                    0.
% 7.07/1.49  orderings_time:                         0.
% 7.07/1.49  out_proof_time:                         0.014
% 7.07/1.49  total_time:                             0.672
% 7.07/1.49  num_of_symbols:                         52
% 7.07/1.49  num_of_terms:                           18657
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing
% 7.07/1.49  
% 7.07/1.49  num_of_splits:                          0
% 7.07/1.49  num_of_split_atoms:                     0
% 7.07/1.49  num_of_reused_defs:                     0
% 7.07/1.49  num_eq_ax_congr_red:                    15
% 7.07/1.49  num_of_sem_filtered_clauses:            2
% 7.07/1.49  num_of_subtypes:                        0
% 7.07/1.49  monotx_restored_types:                  0
% 7.07/1.49  sat_num_of_epr_types:                   0
% 7.07/1.49  sat_num_of_non_cyclic_types:            0
% 7.07/1.49  sat_guarded_non_collapsed_types:        0
% 7.07/1.49  num_pure_diseq_elim:                    0
% 7.07/1.49  simp_replaced_by:                       0
% 7.07/1.49  res_preprocessed:                       150
% 7.07/1.49  prep_upred:                             0
% 7.07/1.49  prep_unflattend:                        35
% 7.07/1.49  smt_new_axioms:                         0
% 7.07/1.49  pred_elim_cands:                        4
% 7.07/1.49  pred_elim:                              3
% 7.07/1.49  pred_elim_cl:                           4
% 7.07/1.49  pred_elim_cycles:                       5
% 7.07/1.49  merged_defs:                            8
% 7.07/1.49  merged_defs_ncl:                        0
% 7.07/1.49  bin_hyper_res:                          10
% 7.07/1.49  prep_cycles:                            4
% 7.07/1.49  pred_elim_time:                         0.005
% 7.07/1.49  splitting_time:                         0.
% 7.07/1.49  sem_filter_time:                        0.
% 7.07/1.49  monotx_time:                            0.
% 7.07/1.49  subtype_inf_time:                       0.
% 7.07/1.49  
% 7.07/1.49  ------ Problem properties
% 7.07/1.49  
% 7.07/1.49  clauses:                                31
% 7.07/1.49  conjectures:                            3
% 7.07/1.49  epr:                                    8
% 7.07/1.49  horn:                                   28
% 7.07/1.49  ground:                                 11
% 7.07/1.49  unary:                                  9
% 7.07/1.49  binary:                                 9
% 7.07/1.49  lits:                                   71
% 7.07/1.49  lits_eq:                                31
% 7.07/1.49  fd_pure:                                0
% 7.07/1.49  fd_pseudo:                              0
% 7.07/1.49  fd_cond:                                5
% 7.07/1.49  fd_pseudo_cond:                         1
% 7.07/1.49  ac_symbols:                             0
% 7.07/1.49  
% 7.07/1.49  ------ Propositional Solver
% 7.07/1.49  
% 7.07/1.49  prop_solver_calls:                      31
% 7.07/1.49  prop_fast_solver_calls:                 1756
% 7.07/1.49  smt_solver_calls:                       0
% 7.07/1.49  smt_fast_solver_calls:                  0
% 7.07/1.49  prop_num_of_clauses:                    9845
% 7.07/1.49  prop_preprocess_simplified:             22737
% 7.07/1.49  prop_fo_subsumed:                       78
% 7.07/1.49  prop_solver_time:                       0.
% 7.07/1.49  smt_solver_time:                        0.
% 7.07/1.49  smt_fast_solver_time:                   0.
% 7.07/1.49  prop_fast_solver_time:                  0.
% 7.07/1.49  prop_unsat_core_time:                   0.
% 7.07/1.49  
% 7.07/1.49  ------ QBF
% 7.07/1.49  
% 7.07/1.49  qbf_q_res:                              0
% 7.07/1.49  qbf_num_tautologies:                    0
% 7.07/1.49  qbf_prep_cycles:                        0
% 7.07/1.49  
% 7.07/1.49  ------ BMC1
% 7.07/1.49  
% 7.07/1.49  bmc1_current_bound:                     -1
% 7.07/1.49  bmc1_last_solved_bound:                 -1
% 7.07/1.49  bmc1_unsat_core_size:                   -1
% 7.07/1.49  bmc1_unsat_core_parents_size:           -1
% 7.07/1.49  bmc1_merge_next_fun:                    0
% 7.07/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation
% 7.07/1.49  
% 7.07/1.49  inst_num_of_clauses:                    2896
% 7.07/1.49  inst_num_in_passive:                    1575
% 7.07/1.49  inst_num_in_active:                     1303
% 7.07/1.49  inst_num_in_unprocessed:                19
% 7.07/1.49  inst_num_of_loops:                      1450
% 7.07/1.49  inst_num_of_learning_restarts:          0
% 7.07/1.49  inst_num_moves_active_passive:          144
% 7.07/1.49  inst_lit_activity:                      0
% 7.07/1.49  inst_lit_activity_moves:                0
% 7.07/1.49  inst_num_tautologies:                   0
% 7.07/1.49  inst_num_prop_implied:                  0
% 7.07/1.49  inst_num_existing_simplified:           0
% 7.07/1.49  inst_num_eq_res_simplified:             0
% 7.07/1.49  inst_num_child_elim:                    0
% 7.07/1.49  inst_num_of_dismatching_blockings:      1797
% 7.07/1.49  inst_num_of_non_proper_insts:           4190
% 7.07/1.49  inst_num_of_duplicates:                 0
% 7.07/1.49  inst_inst_num_from_inst_to_res:         0
% 7.07/1.49  inst_dismatching_checking_time:         0.
% 7.07/1.49  
% 7.07/1.49  ------ Resolution
% 7.07/1.49  
% 7.07/1.49  res_num_of_clauses:                     0
% 7.07/1.49  res_num_in_passive:                     0
% 7.07/1.49  res_num_in_active:                      0
% 7.07/1.49  res_num_of_loops:                       154
% 7.07/1.49  res_forward_subset_subsumed:            251
% 7.07/1.49  res_backward_subset_subsumed:           8
% 7.07/1.49  res_forward_subsumed:                   0
% 7.07/1.49  res_backward_subsumed:                  0
% 7.07/1.49  res_forward_subsumption_resolution:     0
% 7.07/1.49  res_backward_subsumption_resolution:    0
% 7.07/1.49  res_clause_to_clause_subsumption:       3513
% 7.07/1.49  res_orphan_elimination:                 0
% 7.07/1.49  res_tautology_del:                      261
% 7.07/1.49  res_num_eq_res_simplified:              1
% 7.07/1.49  res_num_sel_changes:                    0
% 7.07/1.49  res_moves_from_active_to_pass:          0
% 7.07/1.49  
% 7.07/1.49  ------ Superposition
% 7.07/1.49  
% 7.07/1.49  sup_time_total:                         0.
% 7.07/1.49  sup_time_generating:                    0.
% 7.07/1.49  sup_time_sim_full:                      0.
% 7.07/1.49  sup_time_sim_immed:                     0.
% 7.07/1.49  
% 7.07/1.49  sup_num_of_clauses:                     265
% 7.07/1.49  sup_num_in_active:                      126
% 7.07/1.49  sup_num_in_passive:                     139
% 7.07/1.49  sup_num_of_loops:                       288
% 7.07/1.49  sup_fw_superposition:                   522
% 7.07/1.49  sup_bw_superposition:                   273
% 7.07/1.49  sup_immediate_simplified:               221
% 7.07/1.49  sup_given_eliminated:                   4
% 7.07/1.49  comparisons_done:                       0
% 7.07/1.49  comparisons_avoided:                    171
% 7.07/1.49  
% 7.07/1.49  ------ Simplifications
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  sim_fw_subset_subsumed:                 55
% 7.07/1.49  sim_bw_subset_subsumed:                 14
% 7.07/1.49  sim_fw_subsumed:                        90
% 7.07/1.49  sim_bw_subsumed:                        29
% 7.07/1.49  sim_fw_subsumption_res:                 18
% 7.07/1.49  sim_bw_subsumption_res:                 0
% 7.07/1.49  sim_tautology_del:                      16
% 7.07/1.49  sim_eq_tautology_del:                   124
% 7.07/1.49  sim_eq_res_simp:                        4
% 7.07/1.49  sim_fw_demodulated:                     53
% 7.07/1.49  sim_bw_demodulated:                     163
% 7.07/1.49  sim_light_normalised:                   222
% 7.07/1.49  sim_joinable_taut:                      0
% 7.07/1.49  sim_joinable_simp:                      0
% 7.07/1.49  sim_ac_normalised:                      0
% 7.07/1.49  sim_smt_subsumption:                    0
% 7.07/1.49  
%------------------------------------------------------------------------------
