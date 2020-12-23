%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:37 EST 2020

% Result     : Timeout 59.53s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  224 (6097 expanded)
%              Number of clauses        :  146 (1738 expanded)
%              Number of leaves         :   22 (1581 expanded)
%              Depth                    :   28
%              Number of atoms          :  856 (53526 expanded)
%              Number of equality atoms :  441 (19358 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f44,f49,f48])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f89,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f88,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1265,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1279,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2614,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1265,c_1279])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_506,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_420])).

cnf(c_1257,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1827,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1257])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2195,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1827,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_2620,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2614,c_2195])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3835,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_1268])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2421,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_2422,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2421])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2557,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2558,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2557])).

cnf(c_4484,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3835,c_43,c_45,c_2422,c_2558])).

cnf(c_4490,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4484,c_1279])).

cnf(c_4492,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4490,c_2620])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1269,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1288,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1287,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2571,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1288,c_1287])).

cnf(c_4645,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1269,c_2571])).

cnf(c_4660,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4492,c_4645])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2720,plain,
    ( sK1 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2571,c_30])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1267,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3683,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_1267])).

cnf(c_1262,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1275,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4752,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1275])).

cnf(c_5029,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4752,c_43])).

cnf(c_5030,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5029])).

cnf(c_5042,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_5030])).

cnf(c_1782,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_2674,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_4300,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_5130,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5042,c_39,c_37,c_36,c_34,c_4300])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_407,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_415,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_407,c_16])).

cnf(c_1258,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_5133,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5130,c_1258])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1278,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5159,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_1278])).

cnf(c_6172,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5133,c_40,c_42,c_43,c_45,c_5159])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1273,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5810,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1273,c_2571])).

cnf(c_5822,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_5810])).

cnf(c_5933,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5822,c_40,c_41,c_42])).

cnf(c_5934,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5933])).

cnf(c_5945,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_5934])).

cnf(c_5986,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5945,c_43,c_44,c_45,c_2720])).

cnf(c_6176,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6172,c_5986])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1282,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6347,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6176,c_1282])).

cnf(c_10979,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4660,c_43,c_45,c_2422,c_2558,c_2720,c_3683,c_3835,c_6347])).

cnf(c_4658,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_4645])).

cnf(c_9413,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4658,c_43,c_44,c_45,c_2720,c_6347])).

cnf(c_10981,plain,
    ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_10979,c_9413])).

cnf(c_6,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_10993,plain,
    ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_10981,c_6])).

cnf(c_10995,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_10993,c_6])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1280,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6187,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6172,c_1280])).

cnf(c_2615,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1262,c_1279])).

cnf(c_2617,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2615,c_33])).

cnf(c_6188,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6187,c_2617,c_2620])).

cnf(c_6189,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6188])).

cnf(c_2424,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_2425,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2424])).

cnf(c_2560,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2561,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2560])).

cnf(c_9825,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_funct_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6189,c_40,c_42,c_43,c_45,c_2422,c_2425,c_2558,c_2561,c_6347])).

cnf(c_9826,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2 ),
    inference(renaming,[status(thm)],[c_9825])).

cnf(c_11035,plain,
    ( k2_funct_1(sK4) = sK3
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_10995,c_9826])).

cnf(c_11041,plain,
    ( k2_funct_1(sK4) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_11035])).

cnf(c_9416,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9413,c_1280])).

cnf(c_9417,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9416,c_2620])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_47,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_701,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_107347,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_108771,plain,
    ( v2_funct_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK3)
    | k2_funct_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_107347])).

cnf(c_108772,plain,
    ( k2_funct_1(sK4) != sK3
    | v2_funct_1(k2_funct_1(sK4)) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108771])).

cnf(c_704,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_107353,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_108770,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_107353])).

cnf(c_108774,plain,
    ( k2_funct_1(sK4) != sK3
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108770])).

cnf(c_117749,plain,
    ( v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9417,c_40,c_42,c_43,c_45,c_47,c_2422,c_2425,c_2558,c_2561,c_6189,c_6347,c_10995,c_108772,c_108774])).

cnf(c_117750,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_117749])).

cnf(c_222105,plain,
    ( k2_funct_1(sK3) = sK4
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK2)
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11041,c_117750])).

cnf(c_3836,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2617,c_1268])).

cnf(c_4342,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3836,c_40,c_42,c_2425,c_2561])).

cnf(c_4348,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4342,c_1279])).

cnf(c_4350,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4348,c_2617])).

cnf(c_4659,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4350,c_4645])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2721,plain,
    ( sK2 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2571,c_29])).

cnf(c_3684,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK2) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2617,c_1267])).

cnf(c_9979,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_40,c_42,c_47,c_2425,c_2561,c_2721,c_3684,c_3836])).

cnf(c_4656,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_4645])).

cnf(c_1802,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2166,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2588,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_4741,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4656,c_39,c_38,c_37,c_33,c_31,c_29,c_2588])).

cnf(c_9981,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_9979,c_4741])).

cnf(c_9993,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_9981,c_6])).

cnf(c_9995,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_9993,c_6])).

cnf(c_222114,plain,
    ( k2_funct_1(sK3) = sK4
    | k6_partfun1(sK2) != k6_partfun1(sK2)
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_222105,c_2617,c_9995])).

cnf(c_222115,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_222114])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_222115,c_2561,c_2425,c_28,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 59.53/7.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.53/7.99  
% 59.53/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.53/7.99  
% 59.53/7.99  ------  iProver source info
% 59.53/7.99  
% 59.53/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.53/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.53/7.99  git: non_committed_changes: false
% 59.53/7.99  git: last_make_outside_of_git: false
% 59.53/7.99  
% 59.53/7.99  ------ 
% 59.53/7.99  
% 59.53/7.99  ------ Input Options
% 59.53/7.99  
% 59.53/7.99  --out_options                           all
% 59.53/7.99  --tptp_safe_out                         true
% 59.53/7.99  --problem_path                          ""
% 59.53/7.99  --include_path                          ""
% 59.53/7.99  --clausifier                            res/vclausify_rel
% 59.53/7.99  --clausifier_options                    --mode clausify
% 59.53/7.99  --stdin                                 false
% 59.53/7.99  --stats_out                             all
% 59.53/7.99  
% 59.53/7.99  ------ General Options
% 59.53/7.99  
% 59.53/7.99  --fof                                   false
% 59.53/7.99  --time_out_real                         305.
% 59.53/7.99  --time_out_virtual                      -1.
% 59.53/7.99  --symbol_type_check                     false
% 59.53/7.99  --clausify_out                          false
% 59.53/7.99  --sig_cnt_out                           false
% 59.53/7.99  --trig_cnt_out                          false
% 59.53/7.99  --trig_cnt_out_tolerance                1.
% 59.53/7.99  --trig_cnt_out_sk_spl                   false
% 59.53/7.99  --abstr_cl_out                          false
% 59.53/7.99  
% 59.53/7.99  ------ Global Options
% 59.53/7.99  
% 59.53/7.99  --schedule                              default
% 59.53/7.99  --add_important_lit                     false
% 59.53/7.99  --prop_solver_per_cl                    1000
% 59.53/7.99  --min_unsat_core                        false
% 59.53/7.99  --soft_assumptions                      false
% 59.53/7.99  --soft_lemma_size                       3
% 59.53/7.99  --prop_impl_unit_size                   0
% 59.53/7.99  --prop_impl_unit                        []
% 59.53/7.99  --share_sel_clauses                     true
% 59.53/7.99  --reset_solvers                         false
% 59.53/7.99  --bc_imp_inh                            [conj_cone]
% 59.53/7.99  --conj_cone_tolerance                   3.
% 59.53/7.99  --extra_neg_conj                        none
% 59.53/7.99  --large_theory_mode                     true
% 59.53/7.99  --prolific_symb_bound                   200
% 59.53/7.99  --lt_threshold                          2000
% 59.53/7.99  --clause_weak_htbl                      true
% 59.53/7.99  --gc_record_bc_elim                     false
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing Options
% 59.53/7.99  
% 59.53/7.99  --preprocessing_flag                    true
% 59.53/7.99  --time_out_prep_mult                    0.1
% 59.53/7.99  --splitting_mode                        input
% 59.53/7.99  --splitting_grd                         true
% 59.53/7.99  --splitting_cvd                         false
% 59.53/7.99  --splitting_cvd_svl                     false
% 59.53/7.99  --splitting_nvd                         32
% 59.53/7.99  --sub_typing                            true
% 59.53/7.99  --prep_gs_sim                           true
% 59.53/7.99  --prep_unflatten                        true
% 59.53/7.99  --prep_res_sim                          true
% 59.53/7.99  --prep_upred                            true
% 59.53/7.99  --prep_sem_filter                       exhaustive
% 59.53/7.99  --prep_sem_filter_out                   false
% 59.53/7.99  --pred_elim                             true
% 59.53/7.99  --res_sim_input                         true
% 59.53/7.99  --eq_ax_congr_red                       true
% 59.53/7.99  --pure_diseq_elim                       true
% 59.53/7.99  --brand_transform                       false
% 59.53/7.99  --non_eq_to_eq                          false
% 59.53/7.99  --prep_def_merge                        true
% 59.53/7.99  --prep_def_merge_prop_impl              false
% 59.53/7.99  --prep_def_merge_mbd                    true
% 59.53/7.99  --prep_def_merge_tr_red                 false
% 59.53/7.99  --prep_def_merge_tr_cl                  false
% 59.53/7.99  --smt_preprocessing                     true
% 59.53/7.99  --smt_ac_axioms                         fast
% 59.53/7.99  --preprocessed_out                      false
% 59.53/7.99  --preprocessed_stats                    false
% 59.53/7.99  
% 59.53/7.99  ------ Abstraction refinement Options
% 59.53/7.99  
% 59.53/7.99  --abstr_ref                             []
% 59.53/7.99  --abstr_ref_prep                        false
% 59.53/7.99  --abstr_ref_until_sat                   false
% 59.53/7.99  --abstr_ref_sig_restrict                funpre
% 59.53/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.53/7.99  --abstr_ref_under                       []
% 59.53/7.99  
% 59.53/7.99  ------ SAT Options
% 59.53/7.99  
% 59.53/7.99  --sat_mode                              false
% 59.53/7.99  --sat_fm_restart_options                ""
% 59.53/7.99  --sat_gr_def                            false
% 59.53/7.99  --sat_epr_types                         true
% 59.53/7.99  --sat_non_cyclic_types                  false
% 59.53/7.99  --sat_finite_models                     false
% 59.53/7.99  --sat_fm_lemmas                         false
% 59.53/7.99  --sat_fm_prep                           false
% 59.53/7.99  --sat_fm_uc_incr                        true
% 59.53/7.99  --sat_out_model                         small
% 59.53/7.99  --sat_out_clauses                       false
% 59.53/7.99  
% 59.53/7.99  ------ QBF Options
% 59.53/7.99  
% 59.53/7.99  --qbf_mode                              false
% 59.53/7.99  --qbf_elim_univ                         false
% 59.53/7.99  --qbf_dom_inst                          none
% 59.53/7.99  --qbf_dom_pre_inst                      false
% 59.53/7.99  --qbf_sk_in                             false
% 59.53/7.99  --qbf_pred_elim                         true
% 59.53/7.99  --qbf_split                             512
% 59.53/7.99  
% 59.53/7.99  ------ BMC1 Options
% 59.53/7.99  
% 59.53/7.99  --bmc1_incremental                      false
% 59.53/7.99  --bmc1_axioms                           reachable_all
% 59.53/7.99  --bmc1_min_bound                        0
% 59.53/7.99  --bmc1_max_bound                        -1
% 59.53/7.99  --bmc1_max_bound_default                -1
% 59.53/7.99  --bmc1_symbol_reachability              true
% 59.53/7.99  --bmc1_property_lemmas                  false
% 59.53/7.99  --bmc1_k_induction                      false
% 59.53/7.99  --bmc1_non_equiv_states                 false
% 59.53/7.99  --bmc1_deadlock                         false
% 59.53/7.99  --bmc1_ucm                              false
% 59.53/7.99  --bmc1_add_unsat_core                   none
% 59.53/7.99  --bmc1_unsat_core_children              false
% 59.53/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.53/7.99  --bmc1_out_stat                         full
% 59.53/7.99  --bmc1_ground_init                      false
% 59.53/7.99  --bmc1_pre_inst_next_state              false
% 59.53/7.99  --bmc1_pre_inst_state                   false
% 59.53/7.99  --bmc1_pre_inst_reach_state             false
% 59.53/7.99  --bmc1_out_unsat_core                   false
% 59.53/7.99  --bmc1_aig_witness_out                  false
% 59.53/7.99  --bmc1_verbose                          false
% 59.53/7.99  --bmc1_dump_clauses_tptp                false
% 59.53/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.53/7.99  --bmc1_dump_file                        -
% 59.53/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.53/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.53/7.99  --bmc1_ucm_extend_mode                  1
% 59.53/7.99  --bmc1_ucm_init_mode                    2
% 59.53/7.99  --bmc1_ucm_cone_mode                    none
% 59.53/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.53/7.99  --bmc1_ucm_relax_model                  4
% 59.53/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.53/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.53/7.99  --bmc1_ucm_layered_model                none
% 59.53/7.99  --bmc1_ucm_max_lemma_size               10
% 59.53/7.99  
% 59.53/7.99  ------ AIG Options
% 59.53/7.99  
% 59.53/7.99  --aig_mode                              false
% 59.53/7.99  
% 59.53/7.99  ------ Instantiation Options
% 59.53/7.99  
% 59.53/7.99  --instantiation_flag                    true
% 59.53/7.99  --inst_sos_flag                         false
% 59.53/7.99  --inst_sos_phase                        true
% 59.53/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.53/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.53/7.99  --inst_lit_sel_side                     num_symb
% 59.53/7.99  --inst_solver_per_active                1400
% 59.53/7.99  --inst_solver_calls_frac                1.
% 59.53/7.99  --inst_passive_queue_type               priority_queues
% 59.53/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.53/7.99  --inst_passive_queues_freq              [25;2]
% 59.53/7.99  --inst_dismatching                      true
% 59.53/7.99  --inst_eager_unprocessed_to_passive     true
% 59.53/7.99  --inst_prop_sim_given                   true
% 59.53/7.99  --inst_prop_sim_new                     false
% 59.53/7.99  --inst_subs_new                         false
% 59.53/7.99  --inst_eq_res_simp                      false
% 59.53/7.99  --inst_subs_given                       false
% 59.53/7.99  --inst_orphan_elimination               true
% 59.53/7.99  --inst_learning_loop_flag               true
% 59.53/7.99  --inst_learning_start                   3000
% 59.53/7.99  --inst_learning_factor                  2
% 59.53/7.99  --inst_start_prop_sim_after_learn       3
% 59.53/7.99  --inst_sel_renew                        solver
% 59.53/7.99  --inst_lit_activity_flag                true
% 59.53/7.99  --inst_restr_to_given                   false
% 59.53/7.99  --inst_activity_threshold               500
% 59.53/7.99  --inst_out_proof                        true
% 59.53/7.99  
% 59.53/7.99  ------ Resolution Options
% 59.53/7.99  
% 59.53/7.99  --resolution_flag                       true
% 59.53/7.99  --res_lit_sel                           adaptive
% 59.53/7.99  --res_lit_sel_side                      none
% 59.53/7.99  --res_ordering                          kbo
% 59.53/7.99  --res_to_prop_solver                    active
% 59.53/7.99  --res_prop_simpl_new                    false
% 59.53/7.99  --res_prop_simpl_given                  true
% 59.53/7.99  --res_passive_queue_type                priority_queues
% 59.53/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.53/7.99  --res_passive_queues_freq               [15;5]
% 59.53/7.99  --res_forward_subs                      full
% 59.53/7.99  --res_backward_subs                     full
% 59.53/7.99  --res_forward_subs_resolution           true
% 59.53/7.99  --res_backward_subs_resolution          true
% 59.53/7.99  --res_orphan_elimination                true
% 59.53/7.99  --res_time_limit                        2.
% 59.53/7.99  --res_out_proof                         true
% 59.53/7.99  
% 59.53/7.99  ------ Superposition Options
% 59.53/7.99  
% 59.53/7.99  --superposition_flag                    true
% 59.53/7.99  --sup_passive_queue_type                priority_queues
% 59.53/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.53/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.53/7.99  --demod_completeness_check              fast
% 59.53/7.99  --demod_use_ground                      true
% 59.53/7.99  --sup_to_prop_solver                    passive
% 59.53/7.99  --sup_prop_simpl_new                    true
% 59.53/7.99  --sup_prop_simpl_given                  true
% 59.53/7.99  --sup_fun_splitting                     false
% 59.53/7.99  --sup_smt_interval                      50000
% 59.53/7.99  
% 59.53/7.99  ------ Superposition Simplification Setup
% 59.53/7.99  
% 59.53/7.99  --sup_indices_passive                   []
% 59.53/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.53/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_full_bw                           [BwDemod]
% 59.53/7.99  --sup_immed_triv                        [TrivRules]
% 59.53/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.53/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_immed_bw_main                     []
% 59.53/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.53/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.53/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.53/7.99  
% 59.53/7.99  ------ Combination Options
% 59.53/7.99  
% 59.53/7.99  --comb_res_mult                         3
% 59.53/7.99  --comb_sup_mult                         2
% 59.53/7.99  --comb_inst_mult                        10
% 59.53/7.99  
% 59.53/7.99  ------ Debug Options
% 59.53/7.99  
% 59.53/7.99  --dbg_backtrace                         false
% 59.53/7.99  --dbg_dump_prop_clauses                 false
% 59.53/7.99  --dbg_dump_prop_clauses_file            -
% 59.53/7.99  --dbg_out_stat                          false
% 59.53/7.99  ------ Parsing...
% 59.53/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.53/7.99  ------ Proving...
% 59.53/7.99  ------ Problem Properties 
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  clauses                                 38
% 59.53/7.99  conjectures                             11
% 59.53/7.99  EPR                                     11
% 59.53/7.99  Horn                                    34
% 59.53/7.99  unary                                   19
% 59.53/7.99  binary                                  3
% 59.53/7.99  lits                                    128
% 59.53/7.99  lits eq                                 30
% 59.53/7.99  fd_pure                                 0
% 59.53/7.99  fd_pseudo                               0
% 59.53/7.99  fd_cond                                 5
% 59.53/7.99  fd_pseudo_cond                          2
% 59.53/7.99  AC symbols                              0
% 59.53/7.99  
% 59.53/7.99  ------ Schedule dynamic 5 is on 
% 59.53/7.99  
% 59.53/7.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  ------ 
% 59.53/7.99  Current options:
% 59.53/7.99  ------ 
% 59.53/7.99  
% 59.53/7.99  ------ Input Options
% 59.53/7.99  
% 59.53/7.99  --out_options                           all
% 59.53/7.99  --tptp_safe_out                         true
% 59.53/7.99  --problem_path                          ""
% 59.53/7.99  --include_path                          ""
% 59.53/7.99  --clausifier                            res/vclausify_rel
% 59.53/7.99  --clausifier_options                    --mode clausify
% 59.53/7.99  --stdin                                 false
% 59.53/7.99  --stats_out                             all
% 59.53/7.99  
% 59.53/7.99  ------ General Options
% 59.53/7.99  
% 59.53/7.99  --fof                                   false
% 59.53/7.99  --time_out_real                         305.
% 59.53/7.99  --time_out_virtual                      -1.
% 59.53/7.99  --symbol_type_check                     false
% 59.53/7.99  --clausify_out                          false
% 59.53/7.99  --sig_cnt_out                           false
% 59.53/7.99  --trig_cnt_out                          false
% 59.53/7.99  --trig_cnt_out_tolerance                1.
% 59.53/7.99  --trig_cnt_out_sk_spl                   false
% 59.53/7.99  --abstr_cl_out                          false
% 59.53/7.99  
% 59.53/7.99  ------ Global Options
% 59.53/7.99  
% 59.53/7.99  --schedule                              default
% 59.53/7.99  --add_important_lit                     false
% 59.53/7.99  --prop_solver_per_cl                    1000
% 59.53/7.99  --min_unsat_core                        false
% 59.53/7.99  --soft_assumptions                      false
% 59.53/7.99  --soft_lemma_size                       3
% 59.53/7.99  --prop_impl_unit_size                   0
% 59.53/7.99  --prop_impl_unit                        []
% 59.53/7.99  --share_sel_clauses                     true
% 59.53/7.99  --reset_solvers                         false
% 59.53/7.99  --bc_imp_inh                            [conj_cone]
% 59.53/7.99  --conj_cone_tolerance                   3.
% 59.53/7.99  --extra_neg_conj                        none
% 59.53/7.99  --large_theory_mode                     true
% 59.53/7.99  --prolific_symb_bound                   200
% 59.53/7.99  --lt_threshold                          2000
% 59.53/7.99  --clause_weak_htbl                      true
% 59.53/7.99  --gc_record_bc_elim                     false
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing Options
% 59.53/7.99  
% 59.53/7.99  --preprocessing_flag                    true
% 59.53/7.99  --time_out_prep_mult                    0.1
% 59.53/7.99  --splitting_mode                        input
% 59.53/7.99  --splitting_grd                         true
% 59.53/7.99  --splitting_cvd                         false
% 59.53/7.99  --splitting_cvd_svl                     false
% 59.53/7.99  --splitting_nvd                         32
% 59.53/7.99  --sub_typing                            true
% 59.53/7.99  --prep_gs_sim                           true
% 59.53/7.99  --prep_unflatten                        true
% 59.53/7.99  --prep_res_sim                          true
% 59.53/7.99  --prep_upred                            true
% 59.53/7.99  --prep_sem_filter                       exhaustive
% 59.53/7.99  --prep_sem_filter_out                   false
% 59.53/7.99  --pred_elim                             true
% 59.53/7.99  --res_sim_input                         true
% 59.53/7.99  --eq_ax_congr_red                       true
% 59.53/7.99  --pure_diseq_elim                       true
% 59.53/7.99  --brand_transform                       false
% 59.53/7.99  --non_eq_to_eq                          false
% 59.53/7.99  --prep_def_merge                        true
% 59.53/7.99  --prep_def_merge_prop_impl              false
% 59.53/7.99  --prep_def_merge_mbd                    true
% 59.53/7.99  --prep_def_merge_tr_red                 false
% 59.53/7.99  --prep_def_merge_tr_cl                  false
% 59.53/7.99  --smt_preprocessing                     true
% 59.53/7.99  --smt_ac_axioms                         fast
% 59.53/7.99  --preprocessed_out                      false
% 59.53/7.99  --preprocessed_stats                    false
% 59.53/7.99  
% 59.53/7.99  ------ Abstraction refinement Options
% 59.53/7.99  
% 59.53/7.99  --abstr_ref                             []
% 59.53/7.99  --abstr_ref_prep                        false
% 59.53/7.99  --abstr_ref_until_sat                   false
% 59.53/7.99  --abstr_ref_sig_restrict                funpre
% 59.53/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.53/7.99  --abstr_ref_under                       []
% 59.53/7.99  
% 59.53/7.99  ------ SAT Options
% 59.53/7.99  
% 59.53/7.99  --sat_mode                              false
% 59.53/7.99  --sat_fm_restart_options                ""
% 59.53/7.99  --sat_gr_def                            false
% 59.53/7.99  --sat_epr_types                         true
% 59.53/7.99  --sat_non_cyclic_types                  false
% 59.53/7.99  --sat_finite_models                     false
% 59.53/7.99  --sat_fm_lemmas                         false
% 59.53/7.99  --sat_fm_prep                           false
% 59.53/7.99  --sat_fm_uc_incr                        true
% 59.53/7.99  --sat_out_model                         small
% 59.53/7.99  --sat_out_clauses                       false
% 59.53/7.99  
% 59.53/7.99  ------ QBF Options
% 59.53/7.99  
% 59.53/7.99  --qbf_mode                              false
% 59.53/7.99  --qbf_elim_univ                         false
% 59.53/7.99  --qbf_dom_inst                          none
% 59.53/7.99  --qbf_dom_pre_inst                      false
% 59.53/7.99  --qbf_sk_in                             false
% 59.53/7.99  --qbf_pred_elim                         true
% 59.53/7.99  --qbf_split                             512
% 59.53/7.99  
% 59.53/7.99  ------ BMC1 Options
% 59.53/7.99  
% 59.53/7.99  --bmc1_incremental                      false
% 59.53/7.99  --bmc1_axioms                           reachable_all
% 59.53/7.99  --bmc1_min_bound                        0
% 59.53/7.99  --bmc1_max_bound                        -1
% 59.53/7.99  --bmc1_max_bound_default                -1
% 59.53/7.99  --bmc1_symbol_reachability              true
% 59.53/7.99  --bmc1_property_lemmas                  false
% 59.53/7.99  --bmc1_k_induction                      false
% 59.53/7.99  --bmc1_non_equiv_states                 false
% 59.53/7.99  --bmc1_deadlock                         false
% 59.53/7.99  --bmc1_ucm                              false
% 59.53/7.99  --bmc1_add_unsat_core                   none
% 59.53/7.99  --bmc1_unsat_core_children              false
% 59.53/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.53/7.99  --bmc1_out_stat                         full
% 59.53/7.99  --bmc1_ground_init                      false
% 59.53/7.99  --bmc1_pre_inst_next_state              false
% 59.53/7.99  --bmc1_pre_inst_state                   false
% 59.53/7.99  --bmc1_pre_inst_reach_state             false
% 59.53/7.99  --bmc1_out_unsat_core                   false
% 59.53/7.99  --bmc1_aig_witness_out                  false
% 59.53/7.99  --bmc1_verbose                          false
% 59.53/7.99  --bmc1_dump_clauses_tptp                false
% 59.53/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.53/7.99  --bmc1_dump_file                        -
% 59.53/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.53/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.53/7.99  --bmc1_ucm_extend_mode                  1
% 59.53/7.99  --bmc1_ucm_init_mode                    2
% 59.53/7.99  --bmc1_ucm_cone_mode                    none
% 59.53/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.53/7.99  --bmc1_ucm_relax_model                  4
% 59.53/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.53/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.53/7.99  --bmc1_ucm_layered_model                none
% 59.53/7.99  --bmc1_ucm_max_lemma_size               10
% 59.53/7.99  
% 59.53/7.99  ------ AIG Options
% 59.53/7.99  
% 59.53/7.99  --aig_mode                              false
% 59.53/7.99  
% 59.53/7.99  ------ Instantiation Options
% 59.53/7.99  
% 59.53/7.99  --instantiation_flag                    true
% 59.53/7.99  --inst_sos_flag                         false
% 59.53/7.99  --inst_sos_phase                        true
% 59.53/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.53/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.53/7.99  --inst_lit_sel_side                     none
% 59.53/7.99  --inst_solver_per_active                1400
% 59.53/7.99  --inst_solver_calls_frac                1.
% 59.53/7.99  --inst_passive_queue_type               priority_queues
% 59.53/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.53/7.99  --inst_passive_queues_freq              [25;2]
% 59.53/7.99  --inst_dismatching                      true
% 59.53/7.99  --inst_eager_unprocessed_to_passive     true
% 59.53/7.99  --inst_prop_sim_given                   true
% 59.53/7.99  --inst_prop_sim_new                     false
% 59.53/7.99  --inst_subs_new                         false
% 59.53/7.99  --inst_eq_res_simp                      false
% 59.53/7.99  --inst_subs_given                       false
% 59.53/7.99  --inst_orphan_elimination               true
% 59.53/7.99  --inst_learning_loop_flag               true
% 59.53/7.99  --inst_learning_start                   3000
% 59.53/7.99  --inst_learning_factor                  2
% 59.53/7.99  --inst_start_prop_sim_after_learn       3
% 59.53/7.99  --inst_sel_renew                        solver
% 59.53/7.99  --inst_lit_activity_flag                true
% 59.53/7.99  --inst_restr_to_given                   false
% 59.53/7.99  --inst_activity_threshold               500
% 59.53/7.99  --inst_out_proof                        true
% 59.53/7.99  
% 59.53/7.99  ------ Resolution Options
% 59.53/7.99  
% 59.53/7.99  --resolution_flag                       false
% 59.53/7.99  --res_lit_sel                           adaptive
% 59.53/7.99  --res_lit_sel_side                      none
% 59.53/7.99  --res_ordering                          kbo
% 59.53/7.99  --res_to_prop_solver                    active
% 59.53/7.99  --res_prop_simpl_new                    false
% 59.53/7.99  --res_prop_simpl_given                  true
% 59.53/7.99  --res_passive_queue_type                priority_queues
% 59.53/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.53/7.99  --res_passive_queues_freq               [15;5]
% 59.53/7.99  --res_forward_subs                      full
% 59.53/7.99  --res_backward_subs                     full
% 59.53/7.99  --res_forward_subs_resolution           true
% 59.53/7.99  --res_backward_subs_resolution          true
% 59.53/7.99  --res_orphan_elimination                true
% 59.53/7.99  --res_time_limit                        2.
% 59.53/7.99  --res_out_proof                         true
% 59.53/7.99  
% 59.53/7.99  ------ Superposition Options
% 59.53/7.99  
% 59.53/7.99  --superposition_flag                    true
% 59.53/7.99  --sup_passive_queue_type                priority_queues
% 59.53/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.53/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.53/7.99  --demod_completeness_check              fast
% 59.53/7.99  --demod_use_ground                      true
% 59.53/7.99  --sup_to_prop_solver                    passive
% 59.53/7.99  --sup_prop_simpl_new                    true
% 59.53/7.99  --sup_prop_simpl_given                  true
% 59.53/7.99  --sup_fun_splitting                     false
% 59.53/7.99  --sup_smt_interval                      50000
% 59.53/7.99  
% 59.53/7.99  ------ Superposition Simplification Setup
% 59.53/7.99  
% 59.53/7.99  --sup_indices_passive                   []
% 59.53/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.53/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.53/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_full_bw                           [BwDemod]
% 59.53/7.99  --sup_immed_triv                        [TrivRules]
% 59.53/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.53/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_immed_bw_main                     []
% 59.53/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.53/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.53/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.53/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.53/7.99  
% 59.53/7.99  ------ Combination Options
% 59.53/7.99  
% 59.53/7.99  --comb_res_mult                         3
% 59.53/7.99  --comb_sup_mult                         2
% 59.53/7.99  --comb_inst_mult                        10
% 59.53/7.99  
% 59.53/7.99  ------ Debug Options
% 59.53/7.99  
% 59.53/7.99  --dbg_backtrace                         false
% 59.53/7.99  --dbg_dump_prop_clauses                 false
% 59.53/7.99  --dbg_dump_prop_clauses_file            -
% 59.53/7.99  --dbg_out_stat                          false
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  ------ Proving...
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  % SZS status Theorem for theBenchmark.p
% 59.53/7.99  
% 59.53/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.53/7.99  
% 59.53/7.99  fof(f20,conjecture,(
% 59.53/7.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f21,negated_conjecture,(
% 59.53/7.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.53/7.99    inference(negated_conjecture,[],[f20])).
% 59.53/7.99  
% 59.53/7.99  fof(f43,plain,(
% 59.53/7.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 59.53/7.99    inference(ennf_transformation,[],[f21])).
% 59.53/7.99  
% 59.53/7.99  fof(f44,plain,(
% 59.53/7.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 59.53/7.99    inference(flattening,[],[f43])).
% 59.53/7.99  
% 59.53/7.99  fof(f49,plain,(
% 59.53/7.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 59.53/7.99    introduced(choice_axiom,[])).
% 59.53/7.99  
% 59.53/7.99  fof(f48,plain,(
% 59.53/7.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 59.53/7.99    introduced(choice_axiom,[])).
% 59.53/7.99  
% 59.53/7.99  fof(f50,plain,(
% 59.53/7.99    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 59.53/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f44,f49,f48])).
% 59.53/7.99  
% 59.53/7.99  fof(f85,plain,(
% 59.53/7.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f10,axiom,(
% 59.53/7.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f28,plain,(
% 59.53/7.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.53/7.99    inference(ennf_transformation,[],[f10])).
% 59.53/7.99  
% 59.53/7.99  fof(f62,plain,(
% 59.53/7.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.53/7.99    inference(cnf_transformation,[],[f28])).
% 59.53/7.99  
% 59.53/7.99  fof(f16,axiom,(
% 59.53/7.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f35,plain,(
% 59.53/7.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 59.53/7.99    inference(ennf_transformation,[],[f16])).
% 59.53/7.99  
% 59.53/7.99  fof(f36,plain,(
% 59.53/7.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 59.53/7.99    inference(flattening,[],[f35])).
% 59.53/7.99  
% 59.53/7.99  fof(f70,plain,(
% 59.53/7.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f36])).
% 59.53/7.99  
% 59.53/7.99  fof(f87,plain,(
% 59.53/7.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f80,plain,(
% 59.53/7.99    v1_funct_1(sK3)),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f81,plain,(
% 59.53/7.99    v1_funct_2(sK3,sK1,sK2)),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f82,plain,(
% 59.53/7.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f83,plain,(
% 59.53/7.99    v1_funct_1(sK4)),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f84,plain,(
% 59.53/7.99    v1_funct_2(sK4,sK2,sK1)),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f19,axiom,(
% 59.53/7.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f41,plain,(
% 59.53/7.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.53/7.99    inference(ennf_transformation,[],[f19])).
% 59.53/7.99  
% 59.53/7.99  fof(f42,plain,(
% 59.53/7.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.53/7.99    inference(flattening,[],[f41])).
% 59.53/7.99  
% 59.53/7.99  fof(f79,plain,(
% 59.53/7.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f42])).
% 59.53/7.99  
% 59.53/7.99  fof(f5,axiom,(
% 59.53/7.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f25,plain,(
% 59.53/7.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 59.53/7.99    inference(ennf_transformation,[],[f5])).
% 59.53/7.99  
% 59.53/7.99  fof(f55,plain,(
% 59.53/7.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f25])).
% 59.53/7.99  
% 59.53/7.99  fof(f6,axiom,(
% 59.53/7.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f56,plain,(
% 59.53/7.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.53/7.99    inference(cnf_transformation,[],[f6])).
% 59.53/7.99  
% 59.53/7.99  fof(f18,axiom,(
% 59.53/7.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f39,plain,(
% 59.53/7.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 59.53/7.99    inference(ennf_transformation,[],[f18])).
% 59.53/7.99  
% 59.53/7.99  fof(f40,plain,(
% 59.53/7.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 59.53/7.99    inference(flattening,[],[f39])).
% 59.53/7.99  
% 59.53/7.99  fof(f75,plain,(
% 59.53/7.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f40])).
% 59.53/7.99  
% 59.53/7.99  fof(f1,axiom,(
% 59.53/7.99    v1_xboole_0(o_0_0_xboole_0)),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f51,plain,(
% 59.53/7.99    v1_xboole_0(o_0_0_xboole_0)),
% 59.53/7.99    inference(cnf_transformation,[],[f1])).
% 59.53/7.99  
% 59.53/7.99  fof(f2,axiom,(
% 59.53/7.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f23,plain,(
% 59.53/7.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 59.53/7.99    inference(ennf_transformation,[],[f2])).
% 59.53/7.99  
% 59.53/7.99  fof(f52,plain,(
% 59.53/7.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f23])).
% 59.53/7.99  
% 59.53/7.99  fof(f89,plain,(
% 59.53/7.99    k1_xboole_0 != sK1),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f78,plain,(
% 59.53/7.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f42])).
% 59.53/7.99  
% 59.53/7.99  fof(f14,axiom,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f33,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.53/7.99    inference(ennf_transformation,[],[f14])).
% 59.53/7.99  
% 59.53/7.99  fof(f34,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.53/7.99    inference(flattening,[],[f33])).
% 59.53/7.99  
% 59.53/7.99  fof(f68,plain,(
% 59.53/7.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f34])).
% 59.53/7.99  
% 59.53/7.99  fof(f11,axiom,(
% 59.53/7.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f29,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 59.53/7.99    inference(ennf_transformation,[],[f11])).
% 59.53/7.99  
% 59.53/7.99  fof(f30,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.53/7.99    inference(flattening,[],[f29])).
% 59.53/7.99  
% 59.53/7.99  fof(f47,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.53/7.99    inference(nnf_transformation,[],[f30])).
% 59.53/7.99  
% 59.53/7.99  fof(f63,plain,(
% 59.53/7.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.53/7.99    inference(cnf_transformation,[],[f47])).
% 59.53/7.99  
% 59.53/7.99  fof(f13,axiom,(
% 59.53/7.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f22,plain,(
% 59.53/7.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 59.53/7.99    inference(pure_predicate_removal,[],[f13])).
% 59.53/7.99  
% 59.53/7.99  fof(f67,plain,(
% 59.53/7.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 59.53/7.99    inference(cnf_transformation,[],[f22])).
% 59.53/7.99  
% 59.53/7.99  fof(f12,axiom,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f31,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.53/7.99    inference(ennf_transformation,[],[f12])).
% 59.53/7.99  
% 59.53/7.99  fof(f32,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.53/7.99    inference(flattening,[],[f31])).
% 59.53/7.99  
% 59.53/7.99  fof(f66,plain,(
% 59.53/7.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f32])).
% 59.53/7.99  
% 59.53/7.99  fof(f86,plain,(
% 59.53/7.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f17,axiom,(
% 59.53/7.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f37,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 59.53/7.99    inference(ennf_transformation,[],[f17])).
% 59.53/7.99  
% 59.53/7.99  fof(f38,plain,(
% 59.53/7.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 59.53/7.99    inference(flattening,[],[f37])).
% 59.53/7.99  
% 59.53/7.99  fof(f73,plain,(
% 59.53/7.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f38])).
% 59.53/7.99  
% 59.53/7.99  fof(f8,axiom,(
% 59.53/7.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f60,plain,(
% 59.53/7.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 59.53/7.99    inference(cnf_transformation,[],[f8])).
% 59.53/7.99  
% 59.53/7.99  fof(f15,axiom,(
% 59.53/7.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f69,plain,(
% 59.53/7.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f15])).
% 59.53/7.99  
% 59.53/7.99  fof(f94,plain,(
% 59.53/7.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 59.53/7.99    inference(definition_unfolding,[],[f60,f69])).
% 59.53/7.99  
% 59.53/7.99  fof(f7,axiom,(
% 59.53/7.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f58,plain,(
% 59.53/7.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 59.53/7.99    inference(cnf_transformation,[],[f7])).
% 59.53/7.99  
% 59.53/7.99  fof(f92,plain,(
% 59.53/7.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 59.53/7.99    inference(definition_unfolding,[],[f58,f69])).
% 59.53/7.99  
% 59.53/7.99  fof(f9,axiom,(
% 59.53/7.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 59.53/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.53/7.99  
% 59.53/7.99  fof(f26,plain,(
% 59.53/7.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.53/7.99    inference(ennf_transformation,[],[f9])).
% 59.53/7.99  
% 59.53/7.99  fof(f27,plain,(
% 59.53/7.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.53/7.99    inference(flattening,[],[f26])).
% 59.53/7.99  
% 59.53/7.99  fof(f61,plain,(
% 59.53/7.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.53/7.99    inference(cnf_transformation,[],[f27])).
% 59.53/7.99  
% 59.53/7.99  fof(f96,plain,(
% 59.53/7.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.53/7.99    inference(definition_unfolding,[],[f61,f69])).
% 59.53/7.99  
% 59.53/7.99  fof(f88,plain,(
% 59.53/7.99    v2_funct_1(sK3)),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f90,plain,(
% 59.53/7.99    k1_xboole_0 != sK2),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  fof(f91,plain,(
% 59.53/7.99    k2_funct_1(sK3) != sK4),
% 59.53/7.99    inference(cnf_transformation,[],[f50])).
% 59.53/7.99  
% 59.53/7.99  cnf(c_34,negated_conjecture,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 59.53/7.99      inference(cnf_transformation,[],[f85]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1265,plain,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_11,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f62]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1279,plain,
% 59.53/7.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2614,plain,
% 59.53/7.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_1265,c_1279]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_18,plain,
% 59.53/7.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.53/7.99      | ~ v1_funct_2(X2,X0,X1)
% 59.53/7.99      | ~ v1_funct_2(X3,X1,X0)
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.53/7.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.53/7.99      | ~ v1_funct_1(X2)
% 59.53/7.99      | ~ v1_funct_1(X3)
% 59.53/7.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 59.53/7.99      inference(cnf_transformation,[],[f70]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_32,negated_conjecture,
% 59.53/7.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 59.53/7.99      inference(cnf_transformation,[],[f87]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_419,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,X2)
% 59.53/7.99      | ~ v1_funct_2(X3,X2,X1)
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X3)
% 59.53/7.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 59.53/7.99      | k2_relset_1(X1,X2,X0) = X2
% 59.53/7.99      | k6_partfun1(X2) != k6_partfun1(sK1)
% 59.53/7.99      | sK1 != X2 ),
% 59.53/7.99      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_420,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,sK1)
% 59.53/7.99      | ~ v1_funct_2(X2,sK1,X1)
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 59.53/7.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X2)
% 59.53/7.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 59.53/7.99      | k2_relset_1(X1,sK1,X0) = sK1
% 59.53/7.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 59.53/7.99      inference(unflattening,[status(thm)],[c_419]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_506,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,sK1)
% 59.53/7.99      | ~ v1_funct_2(X2,sK1,X1)
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 59.53/7.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X2)
% 59.53/7.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 59.53/7.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 59.53/7.99      inference(equality_resolution_simp,[status(thm)],[c_420]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1257,plain,
% 59.53/7.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 59.53/7.99      | k2_relset_1(X0,sK1,X2) = sK1
% 59.53/7.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 59.53/7.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 59.53/7.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v1_funct_1(X1) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1827,plain,
% 59.53/7.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 59.53/7.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 59.53/7.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 59.53/7.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 59.53/7.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(equality_resolution,[status(thm)],[c_1257]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_39,negated_conjecture,
% 59.53/7.99      ( v1_funct_1(sK3) ),
% 59.53/7.99      inference(cnf_transformation,[],[f80]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_40,plain,
% 59.53/7.99      ( v1_funct_1(sK3) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_38,negated_conjecture,
% 59.53/7.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 59.53/7.99      inference(cnf_transformation,[],[f81]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_41,plain,
% 59.53/7.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_37,negated_conjecture,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 59.53/7.99      inference(cnf_transformation,[],[f82]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_42,plain,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_36,negated_conjecture,
% 59.53/7.99      ( v1_funct_1(sK4) ),
% 59.53/7.99      inference(cnf_transformation,[],[f83]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_43,plain,
% 59.53/7.99      ( v1_funct_1(sK4) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_35,negated_conjecture,
% 59.53/7.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 59.53/7.99      inference(cnf_transformation,[],[f84]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_44,plain,
% 59.53/7.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_45,plain,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2195,plain,
% 59.53/7.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_1827,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2620,plain,
% 59.53/7.99      ( k2_relat_1(sK4) = sK1 ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_2614,c_2195]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_25,plain,
% 59.53/7.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_relat_1(X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f79]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1268,plain,
% 59.53/7.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 59.53/7.99      | v1_funct_1(X0) != iProver_top
% 59.53/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_3835,plain,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_2620,c_1268]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.53/7.99      | ~ v1_relat_1(X1)
% 59.53/7.99      | v1_relat_1(X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f55]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1644,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | v1_relat_1(X0)
% 59.53/7.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_4]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2421,plain,
% 59.53/7.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 59.53/7.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 59.53/7.99      | v1_relat_1(sK4) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_1644]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2422,plain,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 59.53/7.99      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_2421]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5,plain,
% 59.53/7.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.53/7.99      inference(cnf_transformation,[],[f56]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2557,plain,
% 59.53/7.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_5]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2558,plain,
% 59.53/7.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_2557]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4484,plain,
% 59.53/7.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_3835,c_43,c_45,c_2422,c_2558]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4490,plain,
% 59.53/7.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_4484,c_1279]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4492,plain,
% 59.53/7.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = sK1 ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_4490,c_2620]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_24,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,X2)
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v2_funct_1(X0)
% 59.53/7.99      | k2_relset_1(X1,X2,X0) != X2
% 59.53/7.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 59.53/7.99      | k1_xboole_0 = X2 ),
% 59.53/7.99      inference(cnf_transformation,[],[f75]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1269,plain,
% 59.53/7.99      ( k2_relset_1(X0,X1,X2) != X1
% 59.53/7.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 59.53/7.99      | k1_xboole_0 = X1
% 59.53/7.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v2_funct_1(X2) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_0,plain,
% 59.53/7.99      ( v1_xboole_0(o_0_0_xboole_0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f51]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1288,plain,
% 59.53/7.99      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1,plain,
% 59.53/7.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 59.53/7.99      inference(cnf_transformation,[],[f52]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1287,plain,
% 59.53/7.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2571,plain,
% 59.53/7.99      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_1288,c_1287]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4645,plain,
% 59.53/7.99      ( k2_relset_1(X0,X1,X2) != X1
% 59.53/7.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 59.53/7.99      | o_0_0_xboole_0 = X1
% 59.53/7.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v2_funct_1(X2) != iProver_top ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_1269,c_2571]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4660,plain,
% 59.53/7.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 59.53/7.99      | sK1 = o_0_0_xboole_0
% 59.53/7.99      | v1_funct_2(sK4,k1_relat_1(sK4),sK1) != iProver_top
% 59.53/7.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_4492,c_4645]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_30,negated_conjecture,
% 59.53/7.99      ( k1_xboole_0 != sK1 ),
% 59.53/7.99      inference(cnf_transformation,[],[f89]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2720,plain,
% 59.53/7.99      ( sK1 != o_0_0_xboole_0 ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_2571,c_30]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_26,plain,
% 59.53/7.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_relat_1(X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f78]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1267,plain,
% 59.53/7.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 59.53/7.99      | v1_funct_1(X0) != iProver_top
% 59.53/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_3683,plain,
% 59.53/7.99      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_2620,c_1267]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1262,plain,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_17,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X3)
% 59.53/7.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f68]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1275,plain,
% 59.53/7.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 59.53/7.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 59.53/7.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X5) != iProver_top
% 59.53/7.99      | v1_funct_1(X4) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4752,plain,
% 59.53/7.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_1265,c_1275]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5029,plain,
% 59.53/7.99      ( v1_funct_1(X2) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_4752,c_43]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5030,plain,
% 59.53/7.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top ),
% 59.53/7.99      inference(renaming,[status(thm)],[c_5029]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5042,plain,
% 59.53/7.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_1262,c_5030]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1782,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(sK4)
% 59.53/7.99      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_17]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2186,plain,
% 59.53/7.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.53/7.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 59.53/7.99      | ~ v1_funct_1(sK4)
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_1782]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2674,plain,
% 59.53/7.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 59.53/7.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.53/7.99      | ~ v1_funct_1(sK4)
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | k1_partfun1(X0,X1,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_2186]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4300,plain,
% 59.53/7.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 59.53/7.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 59.53/7.99      | ~ v1_funct_1(sK4)
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_2674]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5130,plain,
% 59.53/7.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_5042,c_39,c_37,c_36,c_34,c_4300]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_13,plain,
% 59.53/7.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 59.53/7.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.53/7.99      | X3 = X2 ),
% 59.53/7.99      inference(cnf_transformation,[],[f63]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_406,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | X3 = X0
% 59.53/7.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 59.53/7.99      | k6_partfun1(sK1) != X3
% 59.53/7.99      | sK1 != X2
% 59.53/7.99      | sK1 != X1 ),
% 59.53/7.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_407,plain,
% 59.53/7.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 59.53/7.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 59.53/7.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 59.53/7.99      inference(unflattening,[status(thm)],[c_406]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_16,plain,
% 59.53/7.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 59.53/7.99      inference(cnf_transformation,[],[f67]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_415,plain,
% 59.53/7.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 59.53/7.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 59.53/7.99      inference(forward_subsumption_resolution,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_407,c_16]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1258,plain,
% 59.53/7.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 59.53/7.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5133,plain,
% 59.53/7.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 59.53/7.99      | m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_5130,c_1258]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_14,plain,
% 59.53/7.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.53/7.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X3) ),
% 59.53/7.99      inference(cnf_transformation,[],[f66]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1278,plain,
% 59.53/7.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.53/7.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 59.53/7.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 59.53/7.99      | v1_funct_1(X0) != iProver_top
% 59.53/7.99      | v1_funct_1(X3) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5159,plain,
% 59.53/7.99      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 59.53/7.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 59.53/7.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_5130,c_1278]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6172,plain,
% 59.53/7.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_5133,c_40,c_42,c_43,c_45,c_5159]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_33,negated_conjecture,
% 59.53/7.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 59.53/7.99      inference(cnf_transformation,[],[f86]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_20,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,X2)
% 59.53/7.99      | ~ v1_funct_2(X3,X4,X1)
% 59.53/7.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X3)
% 59.53/7.99      | v2_funct_1(X0)
% 59.53/7.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 59.53/7.99      | k2_relset_1(X4,X1,X3) != X1
% 59.53/7.99      | k1_xboole_0 = X2 ),
% 59.53/7.99      inference(cnf_transformation,[],[f73]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1273,plain,
% 59.53/7.99      ( k2_relset_1(X0,X1,X2) != X1
% 59.53/7.99      | k1_xboole_0 = X3
% 59.53/7.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 59.53/7.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.53/7.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | v1_funct_1(X4) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v2_funct_1(X4) = iProver_top
% 59.53/7.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5810,plain,
% 59.53/7.99      ( k2_relset_1(X0,X1,X2) != X1
% 59.53/7.99      | o_0_0_xboole_0 = X3
% 59.53/7.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.53/7.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 59.53/7.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.53/7.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 59.53/7.99      | v1_funct_1(X2) != iProver_top
% 59.53/7.99      | v1_funct_1(X4) != iProver_top
% 59.53/7.99      | v2_funct_1(X4) = iProver_top
% 59.53/7.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_1273,c_2571]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5822,plain,
% 59.53/7.99      ( o_0_0_xboole_0 = X0
% 59.53/7.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 59.53/7.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 59.53/7.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 59.53/7.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.53/7.99      | v1_funct_1(X1) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(X1) = iProver_top
% 59.53/7.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_33,c_5810]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5933,plain,
% 59.53/7.99      ( v1_funct_1(X1) != iProver_top
% 59.53/7.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 59.53/7.99      | o_0_0_xboole_0 = X0
% 59.53/7.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 59.53/7.99      | v2_funct_1(X1) = iProver_top
% 59.53/7.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_5822,c_40,c_41,c_42]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5934,plain,
% 59.53/7.99      ( o_0_0_xboole_0 = X0
% 59.53/7.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 59.53/7.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 59.53/7.99      | v1_funct_1(X1) != iProver_top
% 59.53/7.99      | v2_funct_1(X1) = iProver_top
% 59.53/7.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 59.53/7.99      inference(renaming,[status(thm)],[c_5933]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5945,plain,
% 59.53/7.99      ( sK1 = o_0_0_xboole_0
% 59.53/7.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 59.53/7.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) = iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_5130,c_5934]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_5986,plain,
% 59.53/7.99      ( v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) = iProver_top ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_5945,c_43,c_44,c_45,c_2720]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6176,plain,
% 59.53/7.99      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) = iProver_top ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_6172,c_5986]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_8,plain,
% 59.53/7.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 59.53/7.99      inference(cnf_transformation,[],[f94]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1282,plain,
% 59.53/7.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6347,plain,
% 59.53/7.99      ( v2_funct_1(sK4) = iProver_top ),
% 59.53/7.99      inference(forward_subsumption_resolution,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_6176,c_1282]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_10979,plain,
% 59.53/7.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_4660,c_43,c_45,c_2422,c_2558,c_2720,c_3683,c_3835,
% 59.53/7.99                 c_6347]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4658,plain,
% 59.53/7.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 59.53/7.99      | sK1 = o_0_0_xboole_0
% 59.53/7.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 59.53/7.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_2195,c_4645]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9413,plain,
% 59.53/7.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_4658,c_43,c_44,c_45,c_2720,c_6347]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_10981,plain,
% 59.53/7.99      ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_10979,c_9413]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6,plain,
% 59.53/7.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 59.53/7.99      inference(cnf_transformation,[],[f92]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_10993,plain,
% 59.53/7.99      ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_10981,c_6]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_10995,plain,
% 59.53/7.99      ( k1_relat_1(sK4) = sK2 ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_10993,c_6]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_10,plain,
% 59.53/7.99      ( ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v1_funct_1(X1)
% 59.53/7.99      | ~ v2_funct_1(X1)
% 59.53/7.99      | ~ v1_relat_1(X1)
% 59.53/7.99      | ~ v1_relat_1(X0)
% 59.53/7.99      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 59.53/7.99      | k2_funct_1(X1) = X0
% 59.53/7.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 59.53/7.99      inference(cnf_transformation,[],[f96]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1280,plain,
% 59.53/7.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 59.53/7.99      | k2_funct_1(X1) = X0
% 59.53/7.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 59.53/7.99      | v1_funct_1(X0) != iProver_top
% 59.53/7.99      | v1_funct_1(X1) != iProver_top
% 59.53/7.99      | v2_funct_1(X1) != iProver_top
% 59.53/7.99      | v1_relat_1(X0) != iProver_top
% 59.53/7.99      | v1_relat_1(X1) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6187,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3
% 59.53/7.99      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 59.53/7.99      | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_6172,c_1280]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2615,plain,
% 59.53/7.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_1262,c_1279]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2617,plain,
% 59.53/7.99      ( k2_relat_1(sK3) = sK2 ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_2615,c_33]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6188,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3
% 59.53/7.99      | k1_relat_1(sK4) != sK2
% 59.53/7.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_6187,c_2617,c_2620]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_6189,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3
% 59.53/7.99      | k1_relat_1(sK4) != sK2
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(equality_resolution_simp,[status(thm)],[c_6188]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2424,plain,
% 59.53/7.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 59.53/7.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 59.53/7.99      | v1_relat_1(sK3) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_1644]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2425,plain,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.53/7.99      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_2424]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2560,plain,
% 59.53/7.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_5]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2561,plain,
% 59.53/7.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_2560]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9825,plain,
% 59.53/7.99      ( k1_relat_1(sK4) != sK2 | k2_funct_1(sK4) = sK3 ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_6189,c_40,c_42,c_43,c_45,c_2422,c_2425,c_2558,c_2561,
% 59.53/7.99                 c_6347]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9826,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3 | k1_relat_1(sK4) != sK2 ),
% 59.53/7.99      inference(renaming,[status(thm)],[c_9825]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_11035,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3 | sK2 != sK2 ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_10995,c_9826]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_11041,plain,
% 59.53/7.99      ( k2_funct_1(sK4) = sK3 ),
% 59.53/7.99      inference(equality_resolution_simp,[status(thm)],[c_11035]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9416,plain,
% 59.53/7.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 59.53/7.99      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 59.53/7.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 59.53/7.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v2_funct_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_9413,c_1280]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9417,plain,
% 59.53/7.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 59.53/7.99      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 59.53/7.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 59.53/7.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_funct_1(sK4) != iProver_top
% 59.53/7.99      | v2_funct_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | v1_relat_1(sK4) != iProver_top ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_9416,c_2620]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_31,negated_conjecture,
% 59.53/7.99      ( v2_funct_1(sK3) ),
% 59.53/7.99      inference(cnf_transformation,[],[f88]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_47,plain,
% 59.53/7.99      ( v2_funct_1(sK3) = iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_701,plain,
% 59.53/7.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 59.53/7.99      theory(equality) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_107347,plain,
% 59.53/7.99      ( v2_funct_1(X0) | ~ v2_funct_1(sK3) | X0 != sK3 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_701]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_108771,plain,
% 59.53/7.99      ( v2_funct_1(k2_funct_1(sK4))
% 59.53/7.99      | ~ v2_funct_1(sK3)
% 59.53/7.99      | k2_funct_1(sK4) != sK3 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_107347]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_108772,plain,
% 59.53/7.99      ( k2_funct_1(sK4) != sK3
% 59.53/7.99      | v2_funct_1(k2_funct_1(sK4)) = iProver_top
% 59.53/7.99      | v2_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_108771]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_704,plain,
% 59.53/7.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 59.53/7.99      theory(equality) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_107353,plain,
% 59.53/7.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_704]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_108770,plain,
% 59.53/7.99      ( v1_funct_1(k2_funct_1(sK4))
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | k2_funct_1(sK4) != sK3 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_107353]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_108774,plain,
% 59.53/7.99      ( k2_funct_1(sK4) != sK3
% 59.53/7.99      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(predicate_to_equality,[status(thm)],[c_108770]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_117749,plain,
% 59.53/7.99      ( v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 59.53/7.99      | k2_funct_1(k2_funct_1(sK4)) = sK4
% 59.53/7.99      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 59.53/7.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_9417,c_40,c_42,c_43,c_45,c_47,c_2422,c_2425,c_2558,
% 59.53/7.99                 c_2561,c_6189,c_6347,c_10995,c_108772,c_108774]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_117750,plain,
% 59.53/7.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 59.53/7.99      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 59.53/7.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 59.53/7.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 59.53/7.99      inference(renaming,[status(thm)],[c_117749]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_222105,plain,
% 59.53/7.99      ( k2_funct_1(sK3) = sK4
% 59.53/7.99      | k1_relat_1(sK3) != sK1
% 59.53/7.99      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK2)
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_11041,c_117750]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_3836,plain,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_2617,c_1268]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4342,plain,
% 59.53/7.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_3836,c_40,c_42,c_2425,c_2561]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4348,plain,
% 59.53/7.99      ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k2_relat_1(sK3) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_4342,c_1279]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4350,plain,
% 59.53/7.99      ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = sK2 ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_4348,c_2617]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4659,plain,
% 59.53/7.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 59.53/7.99      | sK2 = o_0_0_xboole_0
% 59.53/7.99      | v1_funct_2(sK3,k1_relat_1(sK3),sK2) != iProver_top
% 59.53/7.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_4350,c_4645]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_29,negated_conjecture,
% 59.53/7.99      ( k1_xboole_0 != sK2 ),
% 59.53/7.99      inference(cnf_transformation,[],[f90]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2721,plain,
% 59.53/7.99      ( sK2 != o_0_0_xboole_0 ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_2571,c_29]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_3684,plain,
% 59.53/7.99      ( v1_funct_2(sK3,k1_relat_1(sK3),sK2) = iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_2617,c_1267]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9979,plain,
% 59.53/7.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_4659,c_40,c_42,c_47,c_2425,c_2561,c_2721,c_3684,
% 59.53/7.99                 c_3836]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4656,plain,
% 59.53/7.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 59.53/7.99      | sK2 = o_0_0_xboole_0
% 59.53/7.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 59.53/7.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.53/7.99      | v1_funct_1(sK3) != iProver_top
% 59.53/7.99      | v2_funct_1(sK3) != iProver_top ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_33,c_4645]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_1802,plain,
% 59.53/7.99      ( ~ v1_funct_2(X0,X1,sK2)
% 59.53/7.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 59.53/7.99      | ~ v1_funct_1(X0)
% 59.53/7.99      | ~ v2_funct_1(X0)
% 59.53/7.99      | k2_relset_1(X1,sK2,X0) != sK2
% 59.53/7.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 59.53/7.99      | k1_xboole_0 = sK2 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_24]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2166,plain,
% 59.53/7.99      ( ~ v1_funct_2(sK3,X0,sK2)
% 59.53/7.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | ~ v2_funct_1(sK3)
% 59.53/7.99      | k2_relset_1(X0,sK2,sK3) != sK2
% 59.53/7.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 59.53/7.99      | k1_xboole_0 = sK2 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_1802]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_2588,plain,
% 59.53/7.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 59.53/7.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 59.53/7.99      | ~ v1_funct_1(sK3)
% 59.53/7.99      | ~ v2_funct_1(sK3)
% 59.53/7.99      | k2_relset_1(sK1,sK2,sK3) != sK2
% 59.53/7.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 59.53/7.99      | k1_xboole_0 = sK2 ),
% 59.53/7.99      inference(instantiation,[status(thm)],[c_2166]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_4741,plain,
% 59.53/7.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 59.53/7.99      inference(global_propositional_subsumption,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_4656,c_39,c_38,c_37,c_33,c_31,c_29,c_2588]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9981,plain,
% 59.53/7.99      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 59.53/7.99      inference(light_normalisation,[status(thm)],[c_9979,c_4741]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9993,plain,
% 59.53/7.99      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 59.53/7.99      inference(superposition,[status(thm)],[c_9981,c_6]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_9995,plain,
% 59.53/7.99      ( k1_relat_1(sK3) = sK1 ),
% 59.53/7.99      inference(demodulation,[status(thm)],[c_9993,c_6]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_222114,plain,
% 59.53/7.99      ( k2_funct_1(sK3) = sK4
% 59.53/7.99      | k6_partfun1(sK2) != k6_partfun1(sK2)
% 59.53/7.99      | sK1 != sK1
% 59.53/7.99      | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(light_normalisation,
% 59.53/7.99                [status(thm)],
% 59.53/7.99                [c_222105,c_2617,c_9995]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_222115,plain,
% 59.53/7.99      ( k2_funct_1(sK3) = sK4 | v1_relat_1(sK3) != iProver_top ),
% 59.53/7.99      inference(equality_resolution_simp,[status(thm)],[c_222114]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(c_28,negated_conjecture,
% 59.53/7.99      ( k2_funct_1(sK3) != sK4 ),
% 59.53/7.99      inference(cnf_transformation,[],[f91]) ).
% 59.53/7.99  
% 59.53/7.99  cnf(contradiction,plain,
% 59.53/7.99      ( $false ),
% 59.53/7.99      inference(minisat,[status(thm)],[c_222115,c_2561,c_2425,c_28,c_42]) ).
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.53/7.99  
% 59.53/7.99  ------                               Statistics
% 59.53/7.99  
% 59.53/7.99  ------ General
% 59.53/7.99  
% 59.53/7.99  abstr_ref_over_cycles:                  0
% 59.53/7.99  abstr_ref_under_cycles:                 0
% 59.53/7.99  gc_basic_clause_elim:                   0
% 59.53/7.99  forced_gc_time:                         0
% 59.53/7.99  parsing_time:                           0.013
% 59.53/7.99  unif_index_cands_time:                  0.
% 59.53/7.99  unif_index_add_time:                    0.
% 59.53/7.99  orderings_time:                         0.
% 59.53/7.99  out_proof_time:                         0.042
% 59.53/7.99  total_time:                             7.403
% 59.53/7.99  num_of_symbols:                         54
% 59.53/7.99  num_of_terms:                           180822
% 59.53/7.99  
% 59.53/7.99  ------ Preprocessing
% 59.53/7.99  
% 59.53/7.99  num_of_splits:                          0
% 59.53/7.99  num_of_split_atoms:                     0
% 59.53/7.99  num_of_reused_defs:                     0
% 59.53/7.99  num_eq_ax_congr_red:                    0
% 59.53/7.99  num_of_sem_filtered_clauses:            1
% 59.53/7.99  num_of_subtypes:                        0
% 59.53/7.99  monotx_restored_types:                  0
% 59.53/7.99  sat_num_of_epr_types:                   0
% 59.53/7.99  sat_num_of_non_cyclic_types:            0
% 59.53/7.99  sat_guarded_non_collapsed_types:        0
% 59.53/7.99  num_pure_diseq_elim:                    0
% 59.53/7.99  simp_replaced_by:                       0
% 59.53/7.99  res_preprocessed:                       188
% 59.53/7.99  prep_upred:                             0
% 59.53/7.99  prep_unflattend:                        12
% 59.53/7.99  smt_new_axioms:                         0
% 59.53/7.99  pred_elim_cands:                        6
% 59.53/7.99  pred_elim:                              1
% 59.53/7.99  pred_elim_cl:                           1
% 59.53/7.99  pred_elim_cycles:                       3
% 59.53/7.99  merged_defs:                            0
% 59.53/7.99  merged_defs_ncl:                        0
% 59.53/7.99  bin_hyper_res:                          0
% 59.53/7.99  prep_cycles:                            4
% 59.53/7.99  pred_elim_time:                         0.004
% 59.53/7.99  splitting_time:                         0.
% 59.53/7.99  sem_filter_time:                        0.
% 59.53/7.99  monotx_time:                            0.001
% 59.53/7.99  subtype_inf_time:                       0.
% 59.53/7.99  
% 59.53/7.99  ------ Problem properties
% 59.53/7.99  
% 59.53/7.99  clauses:                                38
% 59.53/7.99  conjectures:                            11
% 59.53/7.99  epr:                                    11
% 59.53/7.99  horn:                                   34
% 59.53/7.99  ground:                                 14
% 59.53/7.99  unary:                                  19
% 59.53/7.99  binary:                                 3
% 59.53/7.99  lits:                                   128
% 59.53/7.99  lits_eq:                                30
% 59.53/7.99  fd_pure:                                0
% 59.53/7.99  fd_pseudo:                              0
% 59.53/7.99  fd_cond:                                5
% 59.53/7.99  fd_pseudo_cond:                         2
% 59.53/7.99  ac_symbols:                             0
% 59.53/7.99  
% 59.53/7.99  ------ Propositional Solver
% 59.53/7.99  
% 59.53/7.99  prop_solver_calls:                      81
% 59.53/7.99  prop_fast_solver_calls:                 6434
% 59.53/7.99  smt_solver_calls:                       0
% 59.53/7.99  smt_fast_solver_calls:                  0
% 59.53/7.99  prop_num_of_clauses:                    80891
% 59.53/7.99  prop_preprocess_simplified:             151559
% 59.53/7.99  prop_fo_subsumed:                       1577
% 59.53/7.99  prop_solver_time:                       0.
% 59.53/7.99  smt_solver_time:                        0.
% 59.53/7.99  smt_fast_solver_time:                   0.
% 59.53/7.99  prop_fast_solver_time:                  0.
% 59.53/7.99  prop_unsat_core_time:                   0.015
% 59.53/7.99  
% 59.53/7.99  ------ QBF
% 59.53/7.99  
% 59.53/7.99  qbf_q_res:                              0
% 59.53/7.99  qbf_num_tautologies:                    0
% 59.53/7.99  qbf_prep_cycles:                        0
% 59.53/7.99  
% 59.53/7.99  ------ BMC1
% 59.53/7.99  
% 59.53/7.99  bmc1_current_bound:                     -1
% 59.53/7.99  bmc1_last_solved_bound:                 -1
% 59.53/7.99  bmc1_unsat_core_size:                   -1
% 59.53/7.99  bmc1_unsat_core_parents_size:           -1
% 59.53/7.99  bmc1_merge_next_fun:                    0
% 59.53/7.99  bmc1_unsat_core_clauses_time:           0.
% 59.53/7.99  
% 59.53/7.99  ------ Instantiation
% 59.53/7.99  
% 59.53/7.99  inst_num_of_clauses:                    11426
% 59.53/7.99  inst_num_in_passive:                    5306
% 59.53/7.99  inst_num_in_active:                     5160
% 59.53/7.99  inst_num_in_unprocessed:                3698
% 59.53/7.99  inst_num_of_loops:                      5599
% 59.53/7.99  inst_num_of_learning_restarts:          1
% 59.53/7.99  inst_num_moves_active_passive:          436
% 59.53/7.99  inst_lit_activity:                      0
% 59.53/7.99  inst_lit_activity_moves:                11
% 59.53/7.99  inst_num_tautologies:                   0
% 59.53/7.99  inst_num_prop_implied:                  0
% 59.53/7.99  inst_num_existing_simplified:           0
% 59.53/7.99  inst_num_eq_res_simplified:             0
% 59.53/7.99  inst_num_child_elim:                    0
% 59.53/7.99  inst_num_of_dismatching_blockings:      4019
% 59.53/7.99  inst_num_of_non_proper_insts:           18618
% 59.53/7.99  inst_num_of_duplicates:                 0
% 59.53/7.99  inst_inst_num_from_inst_to_res:         0
% 59.53/7.99  inst_dismatching_checking_time:         0.
% 59.53/7.99  
% 59.53/7.99  ------ Resolution
% 59.53/7.99  
% 59.53/7.99  res_num_of_clauses:                     55
% 59.53/7.99  res_num_in_passive:                     55
% 59.53/7.99  res_num_in_active:                      0
% 59.53/7.99  res_num_of_loops:                       192
% 59.53/7.99  res_forward_subset_subsumed:            274
% 59.53/7.99  res_backward_subset_subsumed:           0
% 59.53/7.99  res_forward_subsumed:                   0
% 59.53/7.99  res_backward_subsumed:                  0
% 59.53/7.99  res_forward_subsumption_resolution:     2
% 59.53/7.99  res_backward_subsumption_resolution:    0
% 59.53/7.99  res_clause_to_clause_subsumption:       23856
% 59.53/7.99  res_orphan_elimination:                 0
% 59.53/7.99  res_tautology_del:                      173
% 59.53/7.99  res_num_eq_res_simplified:              1
% 59.53/7.99  res_num_sel_changes:                    0
% 59.53/7.99  res_moves_from_active_to_pass:          0
% 59.53/7.99  
% 59.53/7.99  ------ Superposition
% 59.53/7.99  
% 59.53/7.99  sup_time_total:                         0.
% 59.53/7.99  sup_time_generating:                    0.
% 59.53/7.99  sup_time_sim_full:                      0.
% 59.53/7.99  sup_time_sim_immed:                     0.
% 59.53/7.99  
% 59.53/7.99  sup_num_of_clauses:                     10598
% 59.53/7.99  sup_num_in_active:                      1081
% 59.53/7.99  sup_num_in_passive:                     9517
% 59.53/7.99  sup_num_of_loops:                       1119
% 59.53/7.99  sup_fw_superposition:                   4675
% 59.53/7.99  sup_bw_superposition:                   6473
% 59.53/7.99  sup_immediate_simplified:               1130
% 59.53/7.99  sup_given_eliminated:                   3
% 59.53/7.99  comparisons_done:                       0
% 59.53/7.99  comparisons_avoided:                    4
% 59.53/7.99  
% 59.53/7.99  ------ Simplifications
% 59.53/7.99  
% 59.53/7.99  
% 59.53/7.99  sim_fw_subset_subsumed:                 186
% 59.53/7.99  sim_bw_subset_subsumed:                 47
% 59.53/7.99  sim_fw_subsumed:                        39
% 59.53/7.99  sim_bw_subsumed:                        0
% 59.53/7.99  sim_fw_subsumption_res:                 16
% 59.53/7.99  sim_bw_subsumption_res:                 0
% 59.53/7.99  sim_tautology_del:                      1
% 59.53/7.99  sim_eq_tautology_del:                   210
% 59.53/7.99  sim_eq_res_simp:                        3
% 59.53/7.99  sim_fw_demodulated:                     110
% 59.53/7.99  sim_bw_demodulated:                     40
% 59.53/7.99  sim_light_normalised:                   1105
% 59.53/7.99  sim_joinable_taut:                      0
% 59.53/7.99  sim_joinable_simp:                      0
% 59.53/7.99  sim_ac_normalised:                      0
% 59.53/7.99  sim_smt_subsumption:                    0
% 59.53/7.99  
%------------------------------------------------------------------------------
