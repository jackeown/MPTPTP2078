%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:19 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  182 (1066 expanded)
%              Number of clauses        :  111 ( 376 expanded)
%              Number of leaves         :   23 ( 211 expanded)
%              Depth                    :   21
%              Number of atoms          :  539 (4410 expanded)
%              Number of equality atoms :  299 (1686 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(sK5,sK3,sK4)
        | ~ v1_funct_1(sK5) )
      & k1_relset_1(sK3,sK4,sK5) = sK3
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(sK5,sK3,sK4)
      | ~ v1_funct_1(sK5) )
    & k1_relset_1(sK3,sK4,sK5) = sK3
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f50])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f47])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    k1_relset_1(sK3,sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k1_tarski(k1_funct_1(X2,X0)),k1_tarski(k1_funct_1(X2,X1))) = k9_relat_1(X2,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f66,f53,f53])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_865,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_842,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK2(X3,X1,X2),X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK2(X3,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2563,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(X0,sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_854])).

cnf(c_33,negated_conjecture,
    ( k1_relset_1(sK3,sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_848,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3541,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_848])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3601,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_36,c_37,c_38])).

cnf(c_5552,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(X0,sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2563,c_3601])).

cnf(c_9,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1942,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_844])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1954,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1942,c_10])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1955,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1954,c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_111,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_112,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1129,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1211,plain,
    ( ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1210,plain,
    ( v1_funct_1(k7_relat_1(sK5,X0))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1214,plain,
    ( v1_funct_1(k7_relat_1(sK5,X0)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_1216,plain,
    ( v1_funct_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1209,plain,
    ( ~ v1_funct_1(sK5)
    | v1_relat_1(k7_relat_1(sK5,X0))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1218,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_1220,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_410,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1405,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k7_relat_1(sK5,X1))
    | X0 != k7_relat_1(sK5,X1) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_1426,plain,
    ( X0 != k7_relat_1(sK5,X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK5,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_1428,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_414,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1458,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k7_relat_1(sK5,X1))
    | X0 != k7_relat_1(sK5,X1) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_1459,plain,
    ( X0 != k7_relat_1(sK5,X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k7_relat_1(sK5,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_1461,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | v1_funct_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_401,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1801,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK5,X2)
    | k7_relat_1(sK5,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_1802,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_2540,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1955,c_36,c_34,c_37,c_111,c_112,c_1128,c_1129,c_1211,c_1216,c_1220,c_1428,c_1461,c_1802])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK1(X3,X1,X2),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_853,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK1(X3,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK1(X1,k1_xboole_0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_853])).

cnf(c_3209,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(X0,k1_xboole_0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2209])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_tarski(k1_funct_1(X1,X2)),k1_tarski(k1_funct_1(X1,X0))) = k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_860,plain,
    ( k2_xboole_0(k1_tarski(k1_funct_1(X0,X1)),k1_tarski(k1_funct_1(X0,X2))) = k9_relat_1(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3759,plain,
    ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k9_relat_1(k1_xboole_0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_860])).

cnf(c_3777,plain,
    ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k9_relat_1(k1_xboole_0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3759,c_10])).

cnf(c_8,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3778,plain,
    ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3777,c_8])).

cnf(c_4269,plain,
    ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3778,c_36,c_34,c_37,c_111,c_112,c_1128,c_1129,c_1211,c_1216,c_1220,c_1428,c_1461,c_1802])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4278,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4269,c_4])).

cnf(c_6055,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3209,c_4278])).

cnf(c_6059,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5552,c_6055])).

cnf(c_10687,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_865,c_6059])).

cnf(c_400,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1298,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_1628,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_2366,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_2367,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_3604,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3601,c_842])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3612,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3604,c_1])).

cnf(c_3615,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3612])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK1(X3,X1,X2),sK2(X3,X1,X2)) = X3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7045,plain,
    ( ~ r2_hidden(X0,sK5)
    | k4_tarski(sK1(X0,sK3,sK4),sK2(X0,sK3,sK4)) = X0 ),
    inference(resolution,[status(thm)],[c_21,c_34])).

cnf(c_6066,plain,
    ( ~ r2_hidden(X0,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6059])).

cnf(c_7231,plain,
    ( ~ r2_hidden(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7045,c_6066])).

cnf(c_7374,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_7231,c_5])).

cnf(c_7376,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_7374])).

cnf(c_10822,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10687,c_1298,c_2367,c_3615,c_7376])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_855,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1738,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_842,c_855])).

cnf(c_1750,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1738,c_33])).

cnf(c_10847,plain,
    ( k1_relat_1(k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_10822,c_1750])).

cnf(c_10850,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10847,c_10])).

cnf(c_1740,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_855])).

cnf(c_3713,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3612,c_1740])).

cnf(c_3740,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3713,c_1750])).

cnf(c_5062,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3740,c_848])).

cnf(c_5074,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5062,c_2])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3645,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK5,sK3,sK4)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_4027,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | v1_funct_2(sK5,sK3,sK4)
    | sK4 != X1
    | sK3 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3645])).

cnf(c_4028,plain,
    ( sK4 != X0
    | sK3 != X1
    | sK5 != sK5
    | v1_funct_2(sK5,X1,X0) != iProver_top
    | v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4027])).

cnf(c_4030,plain,
    ( sK4 != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK5 != sK5
    | v1_funct_2(sK5,sK3,sK4) = iProver_top
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_1739,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_855])).

cnf(c_3714,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3612,c_1739])).

cnf(c_3737,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK5) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3714,c_1750])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_849,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_962,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_849,c_2])).

cnf(c_4857,plain,
    ( sK3 != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_962])).

cnf(c_5082,plain,
    ( sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5074,c_36,c_37,c_38,c_1298,c_3541,c_3612,c_4030,c_4857])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10850,c_5082])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:53:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.99/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/0.93  
% 3.99/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/0.93  
% 3.99/0.93  ------  iProver source info
% 3.99/0.93  
% 3.99/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.99/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/0.93  git: non_committed_changes: false
% 3.99/0.93  git: last_make_outside_of_git: false
% 3.99/0.93  
% 3.99/0.93  ------ 
% 3.99/0.93  
% 3.99/0.93  ------ Input Options
% 3.99/0.93  
% 3.99/0.93  --out_options                           all
% 3.99/0.93  --tptp_safe_out                         true
% 3.99/0.93  --problem_path                          ""
% 3.99/0.93  --include_path                          ""
% 3.99/0.93  --clausifier                            res/vclausify_rel
% 3.99/0.93  --clausifier_options                    --mode clausify
% 3.99/0.93  --stdin                                 false
% 3.99/0.93  --stats_out                             sel
% 3.99/0.93  
% 3.99/0.93  ------ General Options
% 3.99/0.93  
% 3.99/0.93  --fof                                   false
% 3.99/0.93  --time_out_real                         604.99
% 3.99/0.93  --time_out_virtual                      -1.
% 3.99/0.93  --symbol_type_check                     false
% 3.99/0.93  --clausify_out                          false
% 3.99/0.93  --sig_cnt_out                           false
% 3.99/0.93  --trig_cnt_out                          false
% 3.99/0.93  --trig_cnt_out_tolerance                1.
% 3.99/0.93  --trig_cnt_out_sk_spl                   false
% 3.99/0.93  --abstr_cl_out                          false
% 3.99/0.93  
% 3.99/0.93  ------ Global Options
% 3.99/0.93  
% 3.99/0.93  --schedule                              none
% 3.99/0.93  --add_important_lit                     false
% 3.99/0.93  --prop_solver_per_cl                    1000
% 3.99/0.93  --min_unsat_core                        false
% 3.99/0.93  --soft_assumptions                      false
% 3.99/0.93  --soft_lemma_size                       3
% 3.99/0.93  --prop_impl_unit_size                   0
% 3.99/0.93  --prop_impl_unit                        []
% 3.99/0.93  --share_sel_clauses                     true
% 3.99/0.93  --reset_solvers                         false
% 3.99/0.93  --bc_imp_inh                            [conj_cone]
% 3.99/0.93  --conj_cone_tolerance                   3.
% 3.99/0.93  --extra_neg_conj                        none
% 3.99/0.93  --large_theory_mode                     true
% 3.99/0.93  --prolific_symb_bound                   200
% 3.99/0.93  --lt_threshold                          2000
% 3.99/0.93  --clause_weak_htbl                      true
% 3.99/0.93  --gc_record_bc_elim                     false
% 3.99/0.93  
% 3.99/0.93  ------ Preprocessing Options
% 3.99/0.93  
% 3.99/0.93  --preprocessing_flag                    true
% 3.99/0.93  --time_out_prep_mult                    0.1
% 3.99/0.93  --splitting_mode                        input
% 3.99/0.93  --splitting_grd                         true
% 3.99/0.93  --splitting_cvd                         false
% 3.99/0.93  --splitting_cvd_svl                     false
% 3.99/0.93  --splitting_nvd                         32
% 3.99/0.93  --sub_typing                            true
% 3.99/0.93  --prep_gs_sim                           false
% 3.99/0.93  --prep_unflatten                        true
% 3.99/0.93  --prep_res_sim                          true
% 3.99/0.93  --prep_upred                            true
% 3.99/0.93  --prep_sem_filter                       exhaustive
% 3.99/0.93  --prep_sem_filter_out                   false
% 3.99/0.93  --pred_elim                             false
% 3.99/0.93  --res_sim_input                         true
% 3.99/0.93  --eq_ax_congr_red                       true
% 3.99/0.93  --pure_diseq_elim                       true
% 3.99/0.93  --brand_transform                       false
% 3.99/0.93  --non_eq_to_eq                          false
% 3.99/0.93  --prep_def_merge                        true
% 3.99/0.93  --prep_def_merge_prop_impl              false
% 3.99/0.93  --prep_def_merge_mbd                    true
% 3.99/0.93  --prep_def_merge_tr_red                 false
% 3.99/0.93  --prep_def_merge_tr_cl                  false
% 3.99/0.93  --smt_preprocessing                     true
% 3.99/0.93  --smt_ac_axioms                         fast
% 3.99/0.93  --preprocessed_out                      false
% 3.99/0.93  --preprocessed_stats                    false
% 3.99/0.93  
% 3.99/0.93  ------ Abstraction refinement Options
% 3.99/0.93  
% 3.99/0.93  --abstr_ref                             []
% 3.99/0.93  --abstr_ref_prep                        false
% 3.99/0.93  --abstr_ref_until_sat                   false
% 3.99/0.93  --abstr_ref_sig_restrict                funpre
% 3.99/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.93  --abstr_ref_under                       []
% 3.99/0.93  
% 3.99/0.93  ------ SAT Options
% 3.99/0.93  
% 3.99/0.93  --sat_mode                              false
% 3.99/0.93  --sat_fm_restart_options                ""
% 3.99/0.93  --sat_gr_def                            false
% 3.99/0.93  --sat_epr_types                         true
% 3.99/0.93  --sat_non_cyclic_types                  false
% 3.99/0.93  --sat_finite_models                     false
% 3.99/0.93  --sat_fm_lemmas                         false
% 3.99/0.93  --sat_fm_prep                           false
% 3.99/0.93  --sat_fm_uc_incr                        true
% 3.99/0.93  --sat_out_model                         small
% 3.99/0.93  --sat_out_clauses                       false
% 3.99/0.93  
% 3.99/0.93  ------ QBF Options
% 3.99/0.93  
% 3.99/0.93  --qbf_mode                              false
% 3.99/0.93  --qbf_elim_univ                         false
% 3.99/0.93  --qbf_dom_inst                          none
% 3.99/0.93  --qbf_dom_pre_inst                      false
% 3.99/0.93  --qbf_sk_in                             false
% 3.99/0.93  --qbf_pred_elim                         true
% 3.99/0.93  --qbf_split                             512
% 3.99/0.93  
% 3.99/0.93  ------ BMC1 Options
% 3.99/0.93  
% 3.99/0.93  --bmc1_incremental                      false
% 3.99/0.93  --bmc1_axioms                           reachable_all
% 3.99/0.93  --bmc1_min_bound                        0
% 3.99/0.93  --bmc1_max_bound                        -1
% 3.99/0.93  --bmc1_max_bound_default                -1
% 3.99/0.93  --bmc1_symbol_reachability              true
% 3.99/0.93  --bmc1_property_lemmas                  false
% 3.99/0.93  --bmc1_k_induction                      false
% 3.99/0.93  --bmc1_non_equiv_states                 false
% 3.99/0.93  --bmc1_deadlock                         false
% 3.99/0.93  --bmc1_ucm                              false
% 3.99/0.93  --bmc1_add_unsat_core                   none
% 3.99/0.93  --bmc1_unsat_core_children              false
% 3.99/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.93  --bmc1_out_stat                         full
% 3.99/0.93  --bmc1_ground_init                      false
% 3.99/0.93  --bmc1_pre_inst_next_state              false
% 3.99/0.93  --bmc1_pre_inst_state                   false
% 3.99/0.93  --bmc1_pre_inst_reach_state             false
% 3.99/0.93  --bmc1_out_unsat_core                   false
% 3.99/0.93  --bmc1_aig_witness_out                  false
% 3.99/0.93  --bmc1_verbose                          false
% 3.99/0.93  --bmc1_dump_clauses_tptp                false
% 3.99/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.93  --bmc1_dump_file                        -
% 3.99/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.93  --bmc1_ucm_extend_mode                  1
% 3.99/0.93  --bmc1_ucm_init_mode                    2
% 3.99/0.93  --bmc1_ucm_cone_mode                    none
% 3.99/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.93  --bmc1_ucm_relax_model                  4
% 3.99/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.93  --bmc1_ucm_layered_model                none
% 3.99/0.93  --bmc1_ucm_max_lemma_size               10
% 3.99/0.93  
% 3.99/0.93  ------ AIG Options
% 3.99/0.93  
% 3.99/0.93  --aig_mode                              false
% 3.99/0.93  
% 3.99/0.93  ------ Instantiation Options
% 3.99/0.93  
% 3.99/0.93  --instantiation_flag                    true
% 3.99/0.93  --inst_sos_flag                         false
% 3.99/0.93  --inst_sos_phase                        true
% 3.99/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.93  --inst_lit_sel_side                     num_symb
% 3.99/0.93  --inst_solver_per_active                1400
% 3.99/0.93  --inst_solver_calls_frac                1.
% 3.99/0.93  --inst_passive_queue_type               priority_queues
% 3.99/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.93  --inst_passive_queues_freq              [25;2]
% 3.99/0.93  --inst_dismatching                      true
% 3.99/0.93  --inst_eager_unprocessed_to_passive     true
% 3.99/0.93  --inst_prop_sim_given                   true
% 3.99/0.93  --inst_prop_sim_new                     false
% 3.99/0.93  --inst_subs_new                         false
% 3.99/0.93  --inst_eq_res_simp                      false
% 3.99/0.93  --inst_subs_given                       false
% 3.99/0.93  --inst_orphan_elimination               true
% 3.99/0.93  --inst_learning_loop_flag               true
% 3.99/0.93  --inst_learning_start                   3000
% 3.99/0.93  --inst_learning_factor                  2
% 3.99/0.93  --inst_start_prop_sim_after_learn       3
% 3.99/0.93  --inst_sel_renew                        solver
% 3.99/0.93  --inst_lit_activity_flag                true
% 3.99/0.93  --inst_restr_to_given                   false
% 3.99/0.93  --inst_activity_threshold               500
% 3.99/0.93  --inst_out_proof                        true
% 3.99/0.93  
% 3.99/0.93  ------ Resolution Options
% 3.99/0.93  
% 3.99/0.93  --resolution_flag                       true
% 3.99/0.93  --res_lit_sel                           adaptive
% 3.99/0.93  --res_lit_sel_side                      none
% 3.99/0.93  --res_ordering                          kbo
% 3.99/0.93  --res_to_prop_solver                    active
% 3.99/0.93  --res_prop_simpl_new                    false
% 3.99/0.93  --res_prop_simpl_given                  true
% 3.99/0.93  --res_passive_queue_type                priority_queues
% 3.99/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.93  --res_passive_queues_freq               [15;5]
% 3.99/0.93  --res_forward_subs                      full
% 3.99/0.93  --res_backward_subs                     full
% 3.99/0.93  --res_forward_subs_resolution           true
% 3.99/0.93  --res_backward_subs_resolution          true
% 3.99/0.93  --res_orphan_elimination                true
% 3.99/0.93  --res_time_limit                        2.
% 3.99/0.93  --res_out_proof                         true
% 3.99/0.93  
% 3.99/0.93  ------ Superposition Options
% 3.99/0.93  
% 3.99/0.93  --superposition_flag                    true
% 3.99/0.93  --sup_passive_queue_type                priority_queues
% 3.99/0.93  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.93  --sup_passive_queues_freq               [1;4]
% 3.99/0.93  --demod_completeness_check              fast
% 3.99/0.93  --demod_use_ground                      true
% 3.99/0.93  --sup_to_prop_solver                    passive
% 3.99/0.93  --sup_prop_simpl_new                    true
% 3.99/0.93  --sup_prop_simpl_given                  true
% 3.99/0.93  --sup_fun_splitting                     false
% 3.99/0.93  --sup_smt_interval                      50000
% 3.99/0.93  
% 3.99/0.93  ------ Superposition Simplification Setup
% 3.99/0.93  
% 3.99/0.93  --sup_indices_passive                   []
% 3.99/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_full_bw                           [BwDemod]
% 3.99/0.93  --sup_immed_triv                        [TrivRules]
% 3.99/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_immed_bw_main                     []
% 3.99/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.93  
% 3.99/0.93  ------ Combination Options
% 3.99/0.93  
% 3.99/0.93  --comb_res_mult                         3
% 3.99/0.93  --comb_sup_mult                         2
% 3.99/0.93  --comb_inst_mult                        10
% 3.99/0.93  
% 3.99/0.93  ------ Debug Options
% 3.99/0.93  
% 3.99/0.93  --dbg_backtrace                         false
% 3.99/0.93  --dbg_dump_prop_clauses                 false
% 3.99/0.93  --dbg_dump_prop_clauses_file            -
% 3.99/0.93  --dbg_out_stat                          false
% 3.99/0.93  ------ Parsing...
% 3.99/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/0.93  
% 3.99/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.99/0.93  
% 3.99/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/0.93  
% 3.99/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/0.93  ------ Proving...
% 3.99/0.93  ------ Problem Properties 
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  clauses                                 35
% 3.99/0.93  conjectures                             4
% 3.99/0.93  EPR                                     2
% 3.99/0.93  Horn                                    28
% 3.99/0.93  unary                                   11
% 3.99/0.93  binary                                  3
% 3.99/0.93  lits                                    88
% 3.99/0.93  lits eq                                 27
% 3.99/0.93  fd_pure                                 0
% 3.99/0.93  fd_pseudo                               0
% 3.99/0.93  fd_cond                                 6
% 3.99/0.93  fd_pseudo_cond                          1
% 3.99/0.93  AC symbols                              0
% 3.99/0.93  
% 3.99/0.93  ------ Input Options Time Limit: Unbounded
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  ------ 
% 3.99/0.93  Current options:
% 3.99/0.93  ------ 
% 3.99/0.93  
% 3.99/0.93  ------ Input Options
% 3.99/0.93  
% 3.99/0.93  --out_options                           all
% 3.99/0.93  --tptp_safe_out                         true
% 3.99/0.93  --problem_path                          ""
% 3.99/0.93  --include_path                          ""
% 3.99/0.93  --clausifier                            res/vclausify_rel
% 3.99/0.93  --clausifier_options                    --mode clausify
% 3.99/0.93  --stdin                                 false
% 3.99/0.93  --stats_out                             sel
% 3.99/0.93  
% 3.99/0.93  ------ General Options
% 3.99/0.93  
% 3.99/0.93  --fof                                   false
% 3.99/0.93  --time_out_real                         604.99
% 3.99/0.93  --time_out_virtual                      -1.
% 3.99/0.93  --symbol_type_check                     false
% 3.99/0.93  --clausify_out                          false
% 3.99/0.93  --sig_cnt_out                           false
% 3.99/0.93  --trig_cnt_out                          false
% 3.99/0.93  --trig_cnt_out_tolerance                1.
% 3.99/0.93  --trig_cnt_out_sk_spl                   false
% 3.99/0.93  --abstr_cl_out                          false
% 3.99/0.93  
% 3.99/0.93  ------ Global Options
% 3.99/0.93  
% 3.99/0.93  --schedule                              none
% 3.99/0.93  --add_important_lit                     false
% 3.99/0.93  --prop_solver_per_cl                    1000
% 3.99/0.93  --min_unsat_core                        false
% 3.99/0.93  --soft_assumptions                      false
% 3.99/0.93  --soft_lemma_size                       3
% 3.99/0.93  --prop_impl_unit_size                   0
% 3.99/0.93  --prop_impl_unit                        []
% 3.99/0.93  --share_sel_clauses                     true
% 3.99/0.93  --reset_solvers                         false
% 3.99/0.93  --bc_imp_inh                            [conj_cone]
% 3.99/0.93  --conj_cone_tolerance                   3.
% 3.99/0.93  --extra_neg_conj                        none
% 3.99/0.93  --large_theory_mode                     true
% 3.99/0.93  --prolific_symb_bound                   200
% 3.99/0.93  --lt_threshold                          2000
% 3.99/0.93  --clause_weak_htbl                      true
% 3.99/0.93  --gc_record_bc_elim                     false
% 3.99/0.93  
% 3.99/0.93  ------ Preprocessing Options
% 3.99/0.93  
% 3.99/0.93  --preprocessing_flag                    true
% 3.99/0.93  --time_out_prep_mult                    0.1
% 3.99/0.93  --splitting_mode                        input
% 3.99/0.93  --splitting_grd                         true
% 3.99/0.93  --splitting_cvd                         false
% 3.99/0.93  --splitting_cvd_svl                     false
% 3.99/0.93  --splitting_nvd                         32
% 3.99/0.93  --sub_typing                            true
% 3.99/0.93  --prep_gs_sim                           false
% 3.99/0.93  --prep_unflatten                        true
% 3.99/0.93  --prep_res_sim                          true
% 3.99/0.93  --prep_upred                            true
% 3.99/0.93  --prep_sem_filter                       exhaustive
% 3.99/0.93  --prep_sem_filter_out                   false
% 3.99/0.93  --pred_elim                             false
% 3.99/0.93  --res_sim_input                         true
% 3.99/0.93  --eq_ax_congr_red                       true
% 3.99/0.93  --pure_diseq_elim                       true
% 3.99/0.93  --brand_transform                       false
% 3.99/0.93  --non_eq_to_eq                          false
% 3.99/0.93  --prep_def_merge                        true
% 3.99/0.93  --prep_def_merge_prop_impl              false
% 3.99/0.93  --prep_def_merge_mbd                    true
% 3.99/0.93  --prep_def_merge_tr_red                 false
% 3.99/0.93  --prep_def_merge_tr_cl                  false
% 3.99/0.93  --smt_preprocessing                     true
% 3.99/0.93  --smt_ac_axioms                         fast
% 3.99/0.93  --preprocessed_out                      false
% 3.99/0.93  --preprocessed_stats                    false
% 3.99/0.93  
% 3.99/0.93  ------ Abstraction refinement Options
% 3.99/0.93  
% 3.99/0.93  --abstr_ref                             []
% 3.99/0.93  --abstr_ref_prep                        false
% 3.99/0.93  --abstr_ref_until_sat                   false
% 3.99/0.93  --abstr_ref_sig_restrict                funpre
% 3.99/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.93  --abstr_ref_under                       []
% 3.99/0.93  
% 3.99/0.93  ------ SAT Options
% 3.99/0.93  
% 3.99/0.93  --sat_mode                              false
% 3.99/0.93  --sat_fm_restart_options                ""
% 3.99/0.93  --sat_gr_def                            false
% 3.99/0.93  --sat_epr_types                         true
% 3.99/0.93  --sat_non_cyclic_types                  false
% 3.99/0.93  --sat_finite_models                     false
% 3.99/0.93  --sat_fm_lemmas                         false
% 3.99/0.93  --sat_fm_prep                           false
% 3.99/0.93  --sat_fm_uc_incr                        true
% 3.99/0.93  --sat_out_model                         small
% 3.99/0.93  --sat_out_clauses                       false
% 3.99/0.93  
% 3.99/0.93  ------ QBF Options
% 3.99/0.93  
% 3.99/0.93  --qbf_mode                              false
% 3.99/0.93  --qbf_elim_univ                         false
% 3.99/0.93  --qbf_dom_inst                          none
% 3.99/0.93  --qbf_dom_pre_inst                      false
% 3.99/0.93  --qbf_sk_in                             false
% 3.99/0.93  --qbf_pred_elim                         true
% 3.99/0.93  --qbf_split                             512
% 3.99/0.93  
% 3.99/0.93  ------ BMC1 Options
% 3.99/0.93  
% 3.99/0.93  --bmc1_incremental                      false
% 3.99/0.93  --bmc1_axioms                           reachable_all
% 3.99/0.93  --bmc1_min_bound                        0
% 3.99/0.93  --bmc1_max_bound                        -1
% 3.99/0.93  --bmc1_max_bound_default                -1
% 3.99/0.93  --bmc1_symbol_reachability              true
% 3.99/0.93  --bmc1_property_lemmas                  false
% 3.99/0.93  --bmc1_k_induction                      false
% 3.99/0.93  --bmc1_non_equiv_states                 false
% 3.99/0.93  --bmc1_deadlock                         false
% 3.99/0.93  --bmc1_ucm                              false
% 3.99/0.93  --bmc1_add_unsat_core                   none
% 3.99/0.93  --bmc1_unsat_core_children              false
% 3.99/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.93  --bmc1_out_stat                         full
% 3.99/0.93  --bmc1_ground_init                      false
% 3.99/0.93  --bmc1_pre_inst_next_state              false
% 3.99/0.93  --bmc1_pre_inst_state                   false
% 3.99/0.93  --bmc1_pre_inst_reach_state             false
% 3.99/0.93  --bmc1_out_unsat_core                   false
% 3.99/0.93  --bmc1_aig_witness_out                  false
% 3.99/0.93  --bmc1_verbose                          false
% 3.99/0.93  --bmc1_dump_clauses_tptp                false
% 3.99/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.93  --bmc1_dump_file                        -
% 3.99/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.93  --bmc1_ucm_extend_mode                  1
% 3.99/0.93  --bmc1_ucm_init_mode                    2
% 3.99/0.93  --bmc1_ucm_cone_mode                    none
% 3.99/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.93  --bmc1_ucm_relax_model                  4
% 3.99/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.93  --bmc1_ucm_layered_model                none
% 3.99/0.93  --bmc1_ucm_max_lemma_size               10
% 3.99/0.93  
% 3.99/0.93  ------ AIG Options
% 3.99/0.93  
% 3.99/0.93  --aig_mode                              false
% 3.99/0.93  
% 3.99/0.93  ------ Instantiation Options
% 3.99/0.93  
% 3.99/0.93  --instantiation_flag                    true
% 3.99/0.93  --inst_sos_flag                         false
% 3.99/0.93  --inst_sos_phase                        true
% 3.99/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.93  --inst_lit_sel_side                     num_symb
% 3.99/0.93  --inst_solver_per_active                1400
% 3.99/0.93  --inst_solver_calls_frac                1.
% 3.99/0.93  --inst_passive_queue_type               priority_queues
% 3.99/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.93  --inst_passive_queues_freq              [25;2]
% 3.99/0.93  --inst_dismatching                      true
% 3.99/0.93  --inst_eager_unprocessed_to_passive     true
% 3.99/0.93  --inst_prop_sim_given                   true
% 3.99/0.93  --inst_prop_sim_new                     false
% 3.99/0.93  --inst_subs_new                         false
% 3.99/0.93  --inst_eq_res_simp                      false
% 3.99/0.93  --inst_subs_given                       false
% 3.99/0.93  --inst_orphan_elimination               true
% 3.99/0.93  --inst_learning_loop_flag               true
% 3.99/0.93  --inst_learning_start                   3000
% 3.99/0.93  --inst_learning_factor                  2
% 3.99/0.93  --inst_start_prop_sim_after_learn       3
% 3.99/0.93  --inst_sel_renew                        solver
% 3.99/0.93  --inst_lit_activity_flag                true
% 3.99/0.93  --inst_restr_to_given                   false
% 3.99/0.93  --inst_activity_threshold               500
% 3.99/0.93  --inst_out_proof                        true
% 3.99/0.93  
% 3.99/0.93  ------ Resolution Options
% 3.99/0.93  
% 3.99/0.93  --resolution_flag                       true
% 3.99/0.93  --res_lit_sel                           adaptive
% 3.99/0.93  --res_lit_sel_side                      none
% 3.99/0.93  --res_ordering                          kbo
% 3.99/0.93  --res_to_prop_solver                    active
% 3.99/0.93  --res_prop_simpl_new                    false
% 3.99/0.93  --res_prop_simpl_given                  true
% 3.99/0.93  --res_passive_queue_type                priority_queues
% 3.99/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.93  --res_passive_queues_freq               [15;5]
% 3.99/0.93  --res_forward_subs                      full
% 3.99/0.93  --res_backward_subs                     full
% 3.99/0.93  --res_forward_subs_resolution           true
% 3.99/0.93  --res_backward_subs_resolution          true
% 3.99/0.93  --res_orphan_elimination                true
% 3.99/0.93  --res_time_limit                        2.
% 3.99/0.93  --res_out_proof                         true
% 3.99/0.93  
% 3.99/0.93  ------ Superposition Options
% 3.99/0.93  
% 3.99/0.93  --superposition_flag                    true
% 3.99/0.93  --sup_passive_queue_type                priority_queues
% 3.99/0.93  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.93  --sup_passive_queues_freq               [1;4]
% 3.99/0.93  --demod_completeness_check              fast
% 3.99/0.93  --demod_use_ground                      true
% 3.99/0.93  --sup_to_prop_solver                    passive
% 3.99/0.93  --sup_prop_simpl_new                    true
% 3.99/0.93  --sup_prop_simpl_given                  true
% 3.99/0.93  --sup_fun_splitting                     false
% 3.99/0.93  --sup_smt_interval                      50000
% 3.99/0.93  
% 3.99/0.93  ------ Superposition Simplification Setup
% 3.99/0.93  
% 3.99/0.93  --sup_indices_passive                   []
% 3.99/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_full_bw                           [BwDemod]
% 3.99/0.93  --sup_immed_triv                        [TrivRules]
% 3.99/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_immed_bw_main                     []
% 3.99/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.93  
% 3.99/0.93  ------ Combination Options
% 3.99/0.93  
% 3.99/0.93  --comb_res_mult                         3
% 3.99/0.93  --comb_sup_mult                         2
% 3.99/0.93  --comb_inst_mult                        10
% 3.99/0.93  
% 3.99/0.93  ------ Debug Options
% 3.99/0.93  
% 3.99/0.93  --dbg_backtrace                         false
% 3.99/0.93  --dbg_dump_prop_clauses                 false
% 3.99/0.93  --dbg_dump_prop_clauses_file            -
% 3.99/0.93  --dbg_out_stat                          false
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  ------ Proving...
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  % SZS status Theorem for theBenchmark.p
% 3.99/0.93  
% 3.99/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/0.93  
% 3.99/0.93  fof(f5,axiom,(
% 3.99/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f20,plain,(
% 3.99/0.93    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.99/0.93    inference(ennf_transformation,[],[f5])).
% 3.99/0.93  
% 3.99/0.93  fof(f21,plain,(
% 3.99/0.93    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.99/0.93    inference(flattening,[],[f20])).
% 3.99/0.93  
% 3.99/0.93  fof(f43,plain,(
% 3.99/0.93    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.99/0.93    introduced(choice_axiom,[])).
% 3.99/0.93  
% 3.99/0.93  fof(f44,plain,(
% 3.99/0.93    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.99/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f43])).
% 3.99/0.93  
% 3.99/0.93  fof(f59,plain,(
% 3.99/0.93    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f44])).
% 3.99/0.93  
% 3.99/0.93  fof(f18,conjecture,(
% 3.99/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f19,negated_conjecture,(
% 3.99/0.93    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.99/0.93    inference(negated_conjecture,[],[f18])).
% 3.99/0.93  
% 3.99/0.93  fof(f39,plain,(
% 3.99/0.93    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.99/0.93    inference(ennf_transformation,[],[f19])).
% 3.99/0.93  
% 3.99/0.93  fof(f40,plain,(
% 3.99/0.93    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.99/0.93    inference(flattening,[],[f39])).
% 3.99/0.93  
% 3.99/0.93  fof(f50,plain,(
% 3.99/0.93    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & k1_relset_1(sK3,sK4,sK5) = sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 3.99/0.93    introduced(choice_axiom,[])).
% 3.99/0.93  
% 3.99/0.93  fof(f51,plain,(
% 3.99/0.93    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & k1_relset_1(sK3,sK4,sK5) = sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 3.99/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f50])).
% 3.99/0.93  
% 3.99/0.93  fof(f86,plain,(
% 3.99/0.93    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.99/0.93    inference(cnf_transformation,[],[f51])).
% 3.99/0.93  
% 3.99/0.93  fof(f14,axiom,(
% 3.99/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f31,plain,(
% 3.99/0.93    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.99/0.93    inference(ennf_transformation,[],[f14])).
% 3.99/0.93  
% 3.99/0.93  fof(f32,plain,(
% 3.99/0.93    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.99/0.93    inference(flattening,[],[f31])).
% 3.99/0.93  
% 3.99/0.93  fof(f47,plain,(
% 3.99/0.93    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0))),
% 3.99/0.93    introduced(choice_axiom,[])).
% 3.99/0.93  
% 3.99/0.93  fof(f48,plain,(
% 3.99/0.93    ! [X0,X1,X2,X3] : ((r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.99/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f47])).
% 3.99/0.93  
% 3.99/0.93  fof(f74,plain,(
% 3.99/0.93    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f48])).
% 3.99/0.93  
% 3.99/0.93  fof(f87,plain,(
% 3.99/0.93    k1_relset_1(sK3,sK4,sK5) = sK3),
% 3.99/0.93    inference(cnf_transformation,[],[f51])).
% 3.99/0.93  
% 3.99/0.93  fof(f15,axiom,(
% 3.99/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f33,plain,(
% 3.99/0.93    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/0.93    inference(ennf_transformation,[],[f15])).
% 3.99/0.93  
% 3.99/0.93  fof(f34,plain,(
% 3.99/0.93    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/0.93    inference(flattening,[],[f33])).
% 3.99/0.93  
% 3.99/0.93  fof(f49,plain,(
% 3.99/0.93    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/0.93    inference(nnf_transformation,[],[f34])).
% 3.99/0.93  
% 3.99/0.93  fof(f77,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f49])).
% 3.99/0.93  
% 3.99/0.93  fof(f85,plain,(
% 3.99/0.93    v1_funct_1(sK5)),
% 3.99/0.93    inference(cnf_transformation,[],[f51])).
% 3.99/0.93  
% 3.99/0.93  fof(f88,plain,(
% 3.99/0.93    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)),
% 3.99/0.93    inference(cnf_transformation,[],[f51])).
% 3.99/0.93  
% 3.99/0.93  fof(f8,axiom,(
% 3.99/0.93    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f63,plain,(
% 3.99/0.93    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.99/0.93    inference(cnf_transformation,[],[f8])).
% 3.99/0.93  
% 3.99/0.93  fof(f17,axiom,(
% 3.99/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f37,plain,(
% 3.99/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.99/0.93    inference(ennf_transformation,[],[f17])).
% 3.99/0.93  
% 3.99/0.93  fof(f38,plain,(
% 3.99/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/0.93    inference(flattening,[],[f37])).
% 3.99/0.93  
% 3.99/0.93  fof(f84,plain,(
% 3.99/0.93    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f38])).
% 3.99/0.93  
% 3.99/0.93  fof(f62,plain,(
% 3.99/0.93    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.99/0.93    inference(cnf_transformation,[],[f8])).
% 3.99/0.93  
% 3.99/0.93  fof(f3,axiom,(
% 3.99/0.93    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f41,plain,(
% 3.99/0.93    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.99/0.93    inference(nnf_transformation,[],[f3])).
% 3.99/0.93  
% 3.99/0.93  fof(f42,plain,(
% 3.99/0.93    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.99/0.93    inference(flattening,[],[f41])).
% 3.99/0.93  
% 3.99/0.93  fof(f55,plain,(
% 3.99/0.93    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.99/0.93    inference(cnf_transformation,[],[f42])).
% 3.99/0.93  
% 3.99/0.93  fof(f91,plain,(
% 3.99/0.93    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.99/0.93    inference(equality_resolution,[],[f55])).
% 3.99/0.93  
% 3.99/0.93  fof(f54,plain,(
% 3.99/0.93    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f42])).
% 3.99/0.93  
% 3.99/0.93  fof(f12,axiom,(
% 3.99/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f29,plain,(
% 3.99/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/0.93    inference(ennf_transformation,[],[f12])).
% 3.99/0.93  
% 3.99/0.93  fof(f70,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f29])).
% 3.99/0.93  
% 3.99/0.93  fof(f6,axiom,(
% 3.99/0.93    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f22,plain,(
% 3.99/0.93    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.99/0.93    inference(ennf_transformation,[],[f6])).
% 3.99/0.93  
% 3.99/0.93  fof(f60,plain,(
% 3.99/0.93    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f22])).
% 3.99/0.93  
% 3.99/0.93  fof(f9,axiom,(
% 3.99/0.93    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f23,plain,(
% 3.99/0.93    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.99/0.93    inference(ennf_transformation,[],[f9])).
% 3.99/0.93  
% 3.99/0.93  fof(f24,plain,(
% 3.99/0.93    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/0.93    inference(flattening,[],[f23])).
% 3.99/0.93  
% 3.99/0.93  fof(f65,plain,(
% 3.99/0.93    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f24])).
% 3.99/0.93  
% 3.99/0.93  fof(f64,plain,(
% 3.99/0.93    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f24])).
% 3.99/0.93  
% 3.99/0.93  fof(f73,plain,(
% 3.99/0.93    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f48])).
% 3.99/0.93  
% 3.99/0.93  fof(f10,axiom,(
% 3.99/0.93    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f25,plain,(
% 3.99/0.93    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.99/0.93    inference(ennf_transformation,[],[f10])).
% 3.99/0.93  
% 3.99/0.93  fof(f26,plain,(
% 3.99/0.93    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.99/0.93    inference(flattening,[],[f25])).
% 3.99/0.93  
% 3.99/0.93  fof(f66,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f26])).
% 3.99/0.93  
% 3.99/0.93  fof(f2,axiom,(
% 3.99/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f53,plain,(
% 3.99/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f2])).
% 3.99/0.93  
% 3.99/0.93  fof(f89,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(k1_funct_1(X2,X0)),k1_tarski(k1_funct_1(X2,X1))) = k9_relat_1(X2,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.99/0.93    inference(definition_unfolding,[],[f66,f53,f53])).
% 3.99/0.93  
% 3.99/0.93  fof(f7,axiom,(
% 3.99/0.93    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f61,plain,(
% 3.99/0.93    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f7])).
% 3.99/0.93  
% 3.99/0.93  fof(f4,axiom,(
% 3.99/0.93    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f57,plain,(
% 3.99/0.93    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.99/0.93    inference(cnf_transformation,[],[f4])).
% 3.99/0.93  
% 3.99/0.93  fof(f56,plain,(
% 3.99/0.93    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.99/0.93    inference(cnf_transformation,[],[f42])).
% 3.99/0.93  
% 3.99/0.93  fof(f90,plain,(
% 3.99/0.93    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.99/0.93    inference(equality_resolution,[],[f56])).
% 3.99/0.93  
% 3.99/0.93  fof(f72,plain,(
% 3.99/0.93    ( ! [X2,X0,X3,X1] : (k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f48])).
% 3.99/0.93  
% 3.99/0.93  fof(f13,axiom,(
% 3.99/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.99/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.93  
% 3.99/0.93  fof(f30,plain,(
% 3.99/0.93    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/0.93    inference(ennf_transformation,[],[f13])).
% 3.99/0.93  
% 3.99/0.93  fof(f71,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f30])).
% 3.99/0.93  
% 3.99/0.93  fof(f78,plain,(
% 3.99/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/0.93    inference(cnf_transformation,[],[f49])).
% 3.99/0.93  
% 3.99/0.93  fof(f96,plain,(
% 3.99/0.93    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.99/0.93    inference(equality_resolution,[],[f78])).
% 3.99/0.93  
% 3.99/0.93  cnf(c_5,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.99/0.93      | r2_hidden(sK0(X1,X0),X0)
% 3.99/0.93      | k1_xboole_0 = X0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f59]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_865,plain,
% 3.99/0.93      ( k1_xboole_0 = X0
% 3.99/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.99/0.93      | r2_hidden(sK0(X1,X0),X0) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_34,negated_conjecture,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.99/0.93      inference(cnf_transformation,[],[f86]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_842,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_19,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | ~ r2_hidden(X3,X0)
% 3.99/0.93      | r2_hidden(sK2(X3,X1,X2),X2) ),
% 3.99/0.93      inference(cnf_transformation,[],[f74]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_854,plain,
% 3.99/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.99/0.93      | r2_hidden(X3,X0) != iProver_top
% 3.99/0.93      | r2_hidden(sK2(X3,X1,X2),X2) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2563,plain,
% 3.99/0.93      ( r2_hidden(X0,sK5) != iProver_top
% 3.99/0.93      | r2_hidden(sK2(X0,sK3,sK4),sK4) = iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_842,c_854]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_33,negated_conjecture,
% 3.99/0.93      ( k1_relset_1(sK3,sK4,sK5) = sK3 ),
% 3.99/0.93      inference(cnf_transformation,[],[f87]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_25,plain,
% 3.99/0.93      ( v1_funct_2(X0,X1,X2)
% 3.99/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | k1_relset_1(X1,X2,X0) != X1
% 3.99/0.93      | k1_xboole_0 = X2 ),
% 3.99/0.93      inference(cnf_transformation,[],[f77]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_848,plain,
% 3.99/0.93      ( k1_relset_1(X0,X1,X2) != X0
% 3.99/0.93      | k1_xboole_0 = X1
% 3.99/0.93      | v1_funct_2(X2,X0,X1) = iProver_top
% 3.99/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3541,plain,
% 3.99/0.93      ( sK4 = k1_xboole_0
% 3.99/0.93      | v1_funct_2(sK5,sK3,sK4) = iProver_top
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_33,c_848]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_35,negated_conjecture,
% 3.99/0.93      ( v1_funct_1(sK5) ),
% 3.99/0.93      inference(cnf_transformation,[],[f85]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_36,plain,
% 3.99/0.93      ( v1_funct_1(sK5) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_37,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_32,negated_conjecture,
% 3.99/0.93      ( ~ v1_funct_2(sK5,sK3,sK4)
% 3.99/0.93      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.99/0.93      | ~ v1_funct_1(sK5) ),
% 3.99/0.93      inference(cnf_transformation,[],[f88]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_38,plain,
% 3.99/0.93      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.99/0.93      | v1_funct_1(sK5) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3601,plain,
% 3.99/0.93      ( sK4 = k1_xboole_0 ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_3541,c_36,c_37,c_38]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_5552,plain,
% 3.99/0.93      ( r2_hidden(X0,sK5) != iProver_top
% 3.99/0.93      | r2_hidden(sK2(X0,sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_2563,c_3601]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_9,plain,
% 3.99/0.93      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_29,plain,
% 3.99/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.99/0.93      | ~ v1_funct_1(X0)
% 3.99/0.93      | ~ v1_relat_1(X0) ),
% 3.99/0.93      inference(cnf_transformation,[],[f84]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_844,plain,
% 3.99/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.99/0.93      | v1_funct_1(X0) != iProver_top
% 3.99/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1942,plain,
% 3.99/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_9,c_844]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_10,plain,
% 3.99/0.93      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1954,plain,
% 3.99/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_1942,c_10]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2,plain,
% 3.99/0.93      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f91]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1955,plain,
% 3.99/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(demodulation,[status(thm)],[c_1954,c_2]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3,plain,
% 3.99/0.93      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.99/0.93      | k1_xboole_0 = X1
% 3.99/0.93      | k1_xboole_0 = X0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f54]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_111,plain,
% 3.99/0.93      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.99/0.93      | k1_xboole_0 = k1_xboole_0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_3]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_112,plain,
% 3.99/0.93      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_17,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | v1_relat_1(X0) ),
% 3.99/0.93      inference(cnf_transformation,[],[f70]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1128,plain,
% 3.99/0.93      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.99/0.93      | v1_relat_1(sK5) ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_17]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1129,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.99/0.93      | v1_relat_1(sK5) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_7,plain,
% 3.99/0.93      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1211,plain,
% 3.99/0.93      ( ~ v1_relat_1(sK5) | k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_7]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_11,plain,
% 3.99/0.93      ( ~ v1_funct_1(X0)
% 3.99/0.93      | v1_funct_1(k7_relat_1(X0,X1))
% 3.99/0.93      | ~ v1_relat_1(X0) ),
% 3.99/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1210,plain,
% 3.99/0.93      ( v1_funct_1(k7_relat_1(sK5,X0))
% 3.99/0.93      | ~ v1_funct_1(sK5)
% 3.99/0.93      | ~ v1_relat_1(sK5) ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_11]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1214,plain,
% 3.99/0.93      ( v1_funct_1(k7_relat_1(sK5,X0)) = iProver_top
% 3.99/0.93      | v1_funct_1(sK5) != iProver_top
% 3.99/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1216,plain,
% 3.99/0.93      ( v1_funct_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
% 3.99/0.93      | v1_funct_1(sK5) != iProver_top
% 3.99/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1214]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_12,plain,
% 3.99/0.93      ( ~ v1_funct_1(X0)
% 3.99/0.93      | ~ v1_relat_1(X0)
% 3.99/0.93      | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.99/0.93      inference(cnf_transformation,[],[f64]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1209,plain,
% 3.99/0.93      ( ~ v1_funct_1(sK5)
% 3.99/0.93      | v1_relat_1(k7_relat_1(sK5,X0))
% 3.99/0.93      | ~ v1_relat_1(sK5) ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_12]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1218,plain,
% 3.99/0.93      ( v1_funct_1(sK5) != iProver_top
% 3.99/0.93      | v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top
% 3.99/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1220,plain,
% 3.99/0.93      ( v1_funct_1(sK5) != iProver_top
% 3.99/0.93      | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top
% 3.99/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1218]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_410,plain,
% 3.99/0.93      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.99/0.93      theory(equality) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1405,plain,
% 3.99/0.93      ( v1_relat_1(X0)
% 3.99/0.93      | ~ v1_relat_1(k7_relat_1(sK5,X1))
% 3.99/0.93      | X0 != k7_relat_1(sK5,X1) ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_410]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1426,plain,
% 3.99/0.93      ( X0 != k7_relat_1(sK5,X1)
% 3.99/0.93      | v1_relat_1(X0) = iProver_top
% 3.99/0.93      | v1_relat_1(k7_relat_1(sK5,X1)) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1428,plain,
% 3.99/0.93      ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
% 3.99/0.93      | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1426]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_414,plain,
% 3.99/0.93      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.99/0.93      theory(equality) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1458,plain,
% 3.99/0.93      ( v1_funct_1(X0)
% 3.99/0.93      | ~ v1_funct_1(k7_relat_1(sK5,X1))
% 3.99/0.93      | X0 != k7_relat_1(sK5,X1) ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_414]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1459,plain,
% 3.99/0.93      ( X0 != k7_relat_1(sK5,X1)
% 3.99/0.93      | v1_funct_1(X0) = iProver_top
% 3.99/0.93      | v1_funct_1(k7_relat_1(sK5,X1)) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1461,plain,
% 3.99/0.93      ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
% 3.99/0.93      | v1_funct_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_401,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1801,plain,
% 3.99/0.93      ( X0 != X1 | X0 = k7_relat_1(sK5,X2) | k7_relat_1(sK5,X2) != X1 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_401]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1802,plain,
% 3.99/0.93      ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 3.99/0.93      | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
% 3.99/0.93      | k1_xboole_0 != k1_xboole_0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1801]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2540,plain,
% 3.99/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_1955,c_36,c_34,c_37,c_111,c_112,c_1128,c_1129,c_1211,
% 3.99/0.93                 c_1216,c_1220,c_1428,c_1461,c_1802]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_20,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | ~ r2_hidden(X3,X0)
% 3.99/0.93      | r2_hidden(sK1(X3,X1,X2),X1) ),
% 3.99/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_853,plain,
% 3.99/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.99/0.93      | r2_hidden(X3,X0) != iProver_top
% 3.99/0.93      | r2_hidden(sK1(X3,X1,X2),X1) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2209,plain,
% 3.99/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.99/0.93      | r2_hidden(X1,X0) != iProver_top
% 3.99/0.93      | r2_hidden(sK1(X1,k1_xboole_0,X2),k1_xboole_0) = iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_2,c_853]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3209,plain,
% 3.99/0.93      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.99/0.93      | r2_hidden(sK1(X0,k1_xboole_0,X1),k1_xboole_0) = iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_2540,c_2209]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_13,plain,
% 3.99/0.93      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.99/0.93      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.99/0.93      | ~ v1_funct_1(X1)
% 3.99/0.93      | ~ v1_relat_1(X1)
% 3.99/0.93      | k2_xboole_0(k1_tarski(k1_funct_1(X1,X2)),k1_tarski(k1_funct_1(X1,X0))) = k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) ),
% 3.99/0.93      inference(cnf_transformation,[],[f89]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_860,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(k1_funct_1(X0,X1)),k1_tarski(k1_funct_1(X0,X2))) = k9_relat_1(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
% 3.99/0.93      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.99/0.93      | v1_funct_1(X0) != iProver_top
% 3.99/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3759,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k9_relat_1(k1_xboole_0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
% 3.99/0.93      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_10,c_860]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3777,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k9_relat_1(k1_xboole_0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
% 3.99/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_3759,c_10]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_8,plain,
% 3.99/0.93      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3778,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k1_xboole_0
% 3.99/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.99/0.93      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(demodulation,[status(thm)],[c_3777,c_8]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4269,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(k1_funct_1(k1_xboole_0,X0)),k1_tarski(k1_funct_1(k1_xboole_0,X1))) = k1_xboole_0
% 3.99/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_3778,c_36,c_34,c_37,c_111,c_112,c_1128,c_1129,c_1211,
% 3.99/0.93                 c_1216,c_1220,c_1428,c_1461,c_1802]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4,plain,
% 3.99/0.93      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4278,plain,
% 3.99/0.93      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.99/0.93      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(forward_subsumption_resolution,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_4269,c_4]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_6055,plain,
% 3.99/0.93      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(forward_subsumption_resolution,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_3209,c_4278]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_6059,plain,
% 3.99/0.93      ( r2_hidden(X0,sK5) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_5552,c_6055]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_10687,plain,
% 3.99/0.93      ( sK5 = k1_xboole_0
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_865,c_6059]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_400,plain,( X0 = X0 ),theory(equality) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1298,plain,
% 3.99/0.93      ( sK5 = sK5 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_400]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1628,plain,
% 3.99/0.93      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_401]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2366,plain,
% 3.99/0.93      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_1628]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_2367,plain,
% 3.99/0.93      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_2366]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3604,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.99/0.93      inference(demodulation,[status(thm)],[c_3601,c_842]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1,plain,
% 3.99/0.93      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f90]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3612,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.99/0.93      inference(demodulation,[status(thm)],[c_3604,c_1]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3615,plain,
% 3.99/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
% 3.99/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_3612]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_21,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | ~ r2_hidden(X3,X0)
% 3.99/0.93      | k4_tarski(sK1(X3,X1,X2),sK2(X3,X1,X2)) = X3 ),
% 3.99/0.93      inference(cnf_transformation,[],[f72]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_7045,plain,
% 3.99/0.93      ( ~ r2_hidden(X0,sK5)
% 3.99/0.93      | k4_tarski(sK1(X0,sK3,sK4),sK2(X0,sK3,sK4)) = X0 ),
% 3.99/0.93      inference(resolution,[status(thm)],[c_21,c_34]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_6066,plain,
% 3.99/0.93      ( ~ r2_hidden(X0,sK5) ),
% 3.99/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_6059]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_7231,plain,
% 3.99/0.93      ( ~ r2_hidden(X0,sK5) ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_7045,c_6066]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_7374,plain,
% 3.99/0.93      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | k1_xboole_0 = sK5 ),
% 3.99/0.93      inference(resolution,[status(thm)],[c_7231,c_5]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_7376,plain,
% 3.99/0.93      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK5 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_7374]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_10822,plain,
% 3.99/0.93      ( sK5 = k1_xboole_0 ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_10687,c_1298,c_2367,c_3615,c_7376]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_18,plain,
% 3.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/0.93      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.99/0.93      inference(cnf_transformation,[],[f71]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_855,plain,
% 3.99/0.93      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.99/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1738,plain,
% 3.99/0.93      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_842,c_855]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1750,plain,
% 3.99/0.93      ( k1_relat_1(sK5) = sK3 ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_1738,c_33]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_10847,plain,
% 3.99/0.93      ( k1_relat_1(k1_xboole_0) = sK3 ),
% 3.99/0.93      inference(demodulation,[status(thm)],[c_10822,c_1750]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_10850,plain,
% 3.99/0.93      ( sK3 = k1_xboole_0 ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_10847,c_10]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1740,plain,
% 3.99/0.93      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.99/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_2,c_855]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3713,plain,
% 3.99/0.93      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_3612,c_1740]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3740,plain,
% 3.99/0.93      ( k1_relset_1(k1_xboole_0,X0,sK5) = sK3 ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_3713,c_1750]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_5062,plain,
% 3.99/0.93      ( sK3 != k1_xboole_0
% 3.99/0.93      | k1_xboole_0 = X0
% 3.99/0.93      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_3740,c_848]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_5074,plain,
% 3.99/0.93      ( sK3 != k1_xboole_0
% 3.99/0.93      | k1_xboole_0 = X0
% 3.99/0.93      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_5062,c_2]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_417,plain,
% 3.99/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.99/0.93      | v1_funct_2(X3,X4,X5)
% 3.99/0.93      | X3 != X0
% 3.99/0.93      | X4 != X1
% 3.99/0.93      | X5 != X2 ),
% 3.99/0.93      theory(equality) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3645,plain,
% 3.99/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.99/0.93      | v1_funct_2(sK5,sK3,sK4)
% 3.99/0.93      | sK4 != X2
% 3.99/0.93      | sK3 != X1
% 3.99/0.93      | sK5 != X0 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_417]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4027,plain,
% 3.99/0.93      ( ~ v1_funct_2(sK5,X0,X1)
% 3.99/0.93      | v1_funct_2(sK5,sK3,sK4)
% 3.99/0.93      | sK4 != X1
% 3.99/0.93      | sK3 != X0
% 3.99/0.93      | sK5 != sK5 ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_3645]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4028,plain,
% 3.99/0.93      ( sK4 != X0
% 3.99/0.93      | sK3 != X1
% 3.99/0.93      | sK5 != sK5
% 3.99/0.93      | v1_funct_2(sK5,X1,X0) != iProver_top
% 3.99/0.93      | v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_4027]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4030,plain,
% 3.99/0.93      ( sK4 != k1_xboole_0
% 3.99/0.93      | sK3 != k1_xboole_0
% 3.99/0.93      | sK5 != sK5
% 3.99/0.93      | v1_funct_2(sK5,sK3,sK4) = iProver_top
% 3.99/0.93      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.99/0.93      inference(instantiation,[status(thm)],[c_4028]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_1739,plain,
% 3.99/0.93      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 3.99/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_1,c_855]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3714,plain,
% 3.99/0.93      ( k1_relset_1(X0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_3612,c_1739]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_3737,plain,
% 3.99/0.93      ( k1_relset_1(X0,k1_xboole_0,sK5) = sK3 ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_3714,c_1750]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_24,plain,
% 3.99/0.93      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.99/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.99/0.93      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.99/0.93      inference(cnf_transformation,[],[f96]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_849,plain,
% 3.99/0.93      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.99/0.93      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.99/0.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.99/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_962,plain,
% 3.99/0.93      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.99/0.93      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.99/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.99/0.93      inference(light_normalisation,[status(thm)],[c_849,c_2]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_4857,plain,
% 3.99/0.93      ( sK3 != k1_xboole_0
% 3.99/0.93      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.99/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.99/0.93      inference(superposition,[status(thm)],[c_3737,c_962]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(c_5082,plain,
% 3.99/0.93      ( sK3 != k1_xboole_0 ),
% 3.99/0.93      inference(global_propositional_subsumption,
% 3.99/0.93                [status(thm)],
% 3.99/0.93                [c_5074,c_36,c_37,c_38,c_1298,c_3541,c_3612,c_4030,
% 3.99/0.93                 c_4857]) ).
% 3.99/0.93  
% 3.99/0.93  cnf(contradiction,plain,
% 3.99/0.93      ( $false ),
% 3.99/0.93      inference(minisat,[status(thm)],[c_10850,c_5082]) ).
% 3.99/0.93  
% 3.99/0.93  
% 3.99/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/0.93  
% 3.99/0.93  ------                               Statistics
% 3.99/0.93  
% 3.99/0.93  ------ Selected
% 3.99/0.93  
% 3.99/0.93  total_time:                             0.379
% 3.99/0.93  
%------------------------------------------------------------------------------
