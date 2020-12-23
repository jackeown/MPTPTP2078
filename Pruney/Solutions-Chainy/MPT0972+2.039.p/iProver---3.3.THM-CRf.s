%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:15 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  171 (15435 expanded)
%              Number of clauses        :  104 (4535 expanded)
%              Number of leaves         :   19 (3890 expanded)
%              Depth                    :   33
%              Number of atoms          :  587 (102510 expanded)
%              Number of equality atoms :  308 (25016 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f42,f41])).

fof(f72,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f75,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1072,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1070,c_26])).

cnf(c_2704,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2706,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3057,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2704,c_2706])).

cnf(c_3208,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1072,c_3057])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1080,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_1081,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_1080])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1083,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1081,c_29])).

cnf(c_2702,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3058,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2702,c_2706])).

cnf(c_3233,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1083,c_3058])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2709,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4199,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3208,c_2709])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2915,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2916,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2915])).

cnf(c_4861,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4199,c_35,c_37,c_2916])).

cnf(c_4862,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4861])).

cnf(c_4874,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_4862])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_396,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_2918,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2919,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_2145,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2935,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_3220,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2935])).

cnf(c_2144,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3370,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_4939,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4874,c_32,c_34,c_26,c_396,c_2919,c_3220,c_3370])).

cnf(c_4945,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_4939])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2705,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4961,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4945,c_2705])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2710,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5007,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4961,c_2710])).

cnf(c_5023,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5007])).

cnf(c_6256,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_31,c_29,c_28,c_26,c_396,c_2915,c_2918,c_3220,c_3370,c_5023])).

cnf(c_6260,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3208,c_6256])).

cnf(c_6261,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6260,c_3233])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3450,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_2711])).

cnf(c_6267,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6261,c_3450])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6319,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6267,c_6])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2714,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1023])).

cnf(c_2699,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_2813,plain,
    ( sK5 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2699,c_6])).

cnf(c_6270,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6261,c_2813])).

cnf(c_6301,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6270])).

cnf(c_6278,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6261,c_2702])).

cnf(c_6280,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6278,c_6])).

cnf(c_6305,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6301,c_6280])).

cnf(c_1007,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK6 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1007])).

cnf(c_2700,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_2822,plain,
    ( sK6 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2700,c_6])).

cnf(c_3050,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_3750,plain,
    ( sK6 != X0
    | sK6 = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_3759,plain,
    ( sK6 = sK5
    | sK6 != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_6277,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6261,c_2704])).

cnf(c_6283,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6277,c_6])).

cnf(c_7251,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6305,c_26,c_396,c_2813,c_2822,c_3220,c_3233,c_3370,c_3759,c_6260,c_6280,c_6283])).

cnf(c_7274,plain,
    ( k1_funct_1(sK6,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7251,c_2705])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_521,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_523,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_7345,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7274,c_523])).

cnf(c_7351,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_7345])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2716,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7507,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,k1_xboole_0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7351,c_2716])).

cnf(c_7877,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7507,c_7345])).

cnf(c_7904,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6319,c_7877])).

cnf(c_3449,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_2711])).

cnf(c_6268,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6261,c_3449])).

cnf(c_6316,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6268,c_6])).

cnf(c_7903,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6316,c_7877])).

cnf(c_2936,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2935])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7904,c_7903,c_2936,c_396,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 28
% 3.23/1.00  conjectures                             5
% 3.23/1.00  EPR                                     6
% 3.23/1.00  Horn                                    20
% 3.23/1.00  unary                                   8
% 3.23/1.00  binary                                  10
% 3.23/1.00  lits                                    68
% 3.23/1.00  lits eq                                 29
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 1
% 3.23/1.00  fd_pseudo_cond                          4
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f11,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(flattening,[],[f23])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f62,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f12,conjecture,(
% 3.23/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f13,negated_conjecture,(
% 3.23/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.23/1.00    inference(negated_conjecture,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.23/1.00    inference(ennf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.23/1.00    inference(flattening,[],[f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f42,f41])).
% 3.23/1.00  
% 3.23/1.00  fof(f72,plain,(
% 3.23/1.00    v1_funct_2(sK6,sK3,sK4)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f73,plain,(
% 3.23/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f9,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f59,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f20])).
% 3.23/1.00  
% 3.23/1.00  fof(f69,plain,(
% 3.23/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f70,plain,(
% 3.23/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f6,axiom,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f6])).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f37])).
% 3.23/1.00  
% 3.23/1.00  fof(f55,plain,(
% 3.23/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f38])).
% 3.23/1.00  
% 3.23/1.00  fof(f71,plain,(
% 3.23/1.00    v1_funct_1(sK6)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f19,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f58,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f19])).
% 3.23/1.00  
% 3.23/1.00  fof(f68,plain,(
% 3.23/1.00    v1_funct_1(sK5)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f10,axiom,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.23/1.00    inference(ennf_transformation,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(flattening,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f22])).
% 3.23/1.00  
% 3.23/1.00  fof(f61,plain,(
% 3.23/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f39])).
% 3.23/1.00  
% 3.23/1.00  fof(f78,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(equality_resolution,[],[f61])).
% 3.23/1.00  
% 3.23/1.00  fof(f75,plain,(
% 3.23/1.00    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f74,plain,(
% 3.23/1.00    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f56,plain,(
% 3.23/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f38])).
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f36])).
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/1.00    inference(nnf_transformation,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f35,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/1.00    inference(flattening,[],[f34])).
% 3.23/1.00  
% 3.23/1.00  fof(f52,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f35])).
% 3.23/1.00  
% 3.23/1.00  fof(f76,plain,(
% 3.23/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.23/1.00    inference(equality_resolution,[],[f52])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f15,plain,(
% 3.23/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.23/1.00    inference(ennf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.23/1.00    inference(nnf_transformation,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.23/1.00  
% 3.23/1.00  fof(f47,plain,(
% 3.23/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f66,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f81,plain,(
% 3.23/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.23/1.00    inference(equality_resolution,[],[f66])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f49,plain,(
% 3.23/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.23/1.00    inference(ennf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f57,plain,(
% 3.23/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f14,plain,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(nnf_transformation,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(rectify,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.23/1.00  
% 3.23/1.00  fof(f44,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f30])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_23,plain,
% 3.23/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_27,negated_conjecture,
% 3.23/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.23/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1069,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.00      | sK6 != X0
% 3.23/1.00      | sK4 != X2
% 3.23/1.00      | sK3 != X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1070,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.23/1.00      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.23/1.00      | k1_xboole_0 = sK4 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_1069]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_26,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1072,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1070,c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2704,plain,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_15,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2706,plain,
% 3.23/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.23/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3057,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2704,c_2706]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3208,plain,
% 3.23/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1072,c_3057]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_30,negated_conjecture,
% 3.23/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.23/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1080,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.00      | sK5 != X0
% 3.23/1.00      | sK4 != X2
% 3.23/1.00      | sK3 != X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1081,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.23/1.00      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.23/1.00      | k1_xboole_0 = sK4 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_1080]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_29,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1083,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1081,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2702,plain,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3058,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2702,c_2706]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3233,plain,
% 3.23/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1083,c_3058]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_12,plain,
% 3.23/1.00      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.23/1.00      | ~ v1_relat_1(X1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X1)
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | X1 = X0
% 3.23/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2709,plain,
% 3.23/1.00      ( X0 = X1
% 3.23/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.23/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.23/1.00      | v1_relat_1(X1) != iProver_top
% 3.23/1.00      | v1_relat_1(X0) != iProver_top
% 3.23/1.00      | v1_funct_1(X0) != iProver_top
% 3.23/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4199,plain,
% 3.23/1.00      ( k1_relat_1(X0) != sK3
% 3.23/1.00      | sK6 = X0
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.23/1.00      | v1_relat_1(X0) != iProver_top
% 3.23/1.00      | v1_relat_1(sK6) != iProver_top
% 3.23/1.00      | v1_funct_1(X0) != iProver_top
% 3.23/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3208,c_2709]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_28,negated_conjecture,
% 3.23/1.00      ( v1_funct_1(sK6) ),
% 3.23/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_35,plain,
% 3.23/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_37,plain,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_14,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2915,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.23/1.00      | v1_relat_1(sK6) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2916,plain,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.23/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2915]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4861,plain,
% 3.23/1.00      ( v1_funct_1(X0) != iProver_top
% 3.23/1.00      | k1_relat_1(X0) != sK3
% 3.23/1.00      | sK6 = X0
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.23/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_4199,c_35,c_37,c_2916]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4862,plain,
% 3.23/1.00      ( k1_relat_1(X0) != sK3
% 3.23/1.00      | sK6 = X0
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.23/1.00      | v1_relat_1(X0) != iProver_top
% 3.23/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_4861]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4874,plain,
% 3.23/1.00      ( sK6 = sK5
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 3.23/1.00      | v1_relat_1(sK5) != iProver_top
% 3.23/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3233,c_4862]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_31,negated_conjecture,
% 3.23/1.00      ( v1_funct_1(sK5) ),
% 3.23/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_32,plain,
% 3.23/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_34,plain,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_16,plain,
% 3.23/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.23/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_24,negated_conjecture,
% 3.23/1.00      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.23/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_395,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | sK6 != X0
% 3.23/1.00      | sK5 != X0
% 3.23/1.00      | sK4 != X2
% 3.23/1.00      | sK3 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_396,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.23/1.00      | sK5 != sK6 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2918,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.23/1.00      | v1_relat_1(sK5) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2919,plain,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.23/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2918]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2145,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2935,plain,
% 3.23/1.00      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2145]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3220,plain,
% 3.23/1.00      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2935]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2144,plain,( X0 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3370,plain,
% 3.23/1.00      ( sK5 = sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2144]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4939,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0
% 3.23/1.00      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_4874,c_32,c_34,c_26,c_396,c_2919,c_3220,c_3370]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4945,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3233,c_4939]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_25,negated_conjecture,
% 3.23/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2705,plain,
% 3.23/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 3.23/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4961,plain,
% 3.23/1.00      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 3.23/1.00      | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_4945,c_2705]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_11,plain,
% 3.23/1.00      ( ~ v1_relat_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X1)
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X1)
% 3.23/1.00      | X0 = X1
% 3.23/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.23/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2710,plain,
% 3.23/1.00      ( X0 = X1
% 3.23/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.23/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.23/1.00      | v1_relat_1(X0) != iProver_top
% 3.23/1.00      | v1_relat_1(X1) != iProver_top
% 3.23/1.00      | v1_funct_1(X1) != iProver_top
% 3.23/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5007,plain,
% 3.23/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.23/1.00      | sK6 = sK5
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | v1_relat_1(sK6) != iProver_top
% 3.23/1.00      | v1_relat_1(sK5) != iProver_top
% 3.23/1.00      | v1_funct_1(sK6) != iProver_top
% 3.23/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_4961,c_2710]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5023,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK6)
% 3.23/1.00      | ~ v1_relat_1(sK5)
% 3.23/1.00      | ~ v1_funct_1(sK6)
% 3.23/1.00      | ~ v1_funct_1(sK5)
% 3.23/1.00      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.23/1.00      | sK6 = sK5
% 3.23/1.00      | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5007]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6256,plain,
% 3.23/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5007,c_31,c_29,c_28,c_26,c_396,c_2915,c_2918,c_3220,
% 3.23/1.00                 c_3370,c_5023]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6260,plain,
% 3.23/1.00      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3208,c_6256]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6261,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6260,c_3233]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_10,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2711,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3450,plain,
% 3.23/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2702,c_2711]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6267,plain,
% 3.23/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6261,c_3450]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6,plain,
% 3.23/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6319,plain,
% 3.23/1.00      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6267,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4,plain,
% 3.23/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2714,plain,
% 3.23/1.00      ( X0 = X1
% 3.23/1.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 3.23/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_19,plain,
% 3.23/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.23/1.00      | k1_xboole_0 = X1
% 3.23/1.00      | k1_xboole_0 = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1023,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.23/1.00      | sK5 != X0
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | sK3 != X1
% 3.23/1.00      | k1_xboole_0 = X1
% 3.23/1.00      | k1_xboole_0 = X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1024,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = sK5
% 3.23/1.00      | k1_xboole_0 = sK3 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_1023]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2699,plain,
% 3.23/1.00      ( sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = sK5
% 3.23/1.00      | k1_xboole_0 = sK3
% 3.23/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2813,plain,
% 3.23/1.00      ( sK5 = k1_xboole_0
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | sK3 = k1_xboole_0
% 3.23/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_2699,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6270,plain,
% 3.23/1.00      ( sK5 = k1_xboole_0
% 3.23/1.00      | sK3 = k1_xboole_0
% 3.23/1.00      | k1_xboole_0 != k1_xboole_0
% 3.23/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6261,c_2813]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6301,plain,
% 3.23/1.00      ( sK5 = k1_xboole_0
% 3.23/1.00      | sK3 = k1_xboole_0
% 3.23/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/1.00      inference(equality_resolution_simp,[status(thm)],[c_6270]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6278,plain,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6261,c_2702]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6280,plain,
% 3.23/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6278,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6305,plain,
% 3.23/1.00      ( sK5 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.23/1.00      inference(forward_subsumption_resolution,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6301,c_6280]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1007,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.23/1.00      | sK6 != X0
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | sK3 != X1
% 3.23/1.00      | k1_xboole_0 = X1
% 3.23/1.00      | k1_xboole_0 = X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1008,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = sK6
% 3.23/1.00      | k1_xboole_0 = sK3 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_1007]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2700,plain,
% 3.23/1.00      ( sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = sK6
% 3.23/1.00      | k1_xboole_0 = sK3
% 3.23/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2822,plain,
% 3.23/1.00      ( sK6 = k1_xboole_0
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | sK3 = k1_xboole_0
% 3.23/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_2700,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3050,plain,
% 3.23/1.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2145]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3750,plain,
% 3.23/1.00      ( sK6 != X0 | sK6 = sK5 | sK5 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3050]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3759,plain,
% 3.23/1.00      ( sK6 = sK5 | sK6 != k1_xboole_0 | sK5 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3750]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6277,plain,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6261,c_2704]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6283,plain,
% 3.23/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6277,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7251,plain,
% 3.23/1.00      ( sK3 = k1_xboole_0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6305,c_26,c_396,c_2813,c_2822,c_3220,c_3233,c_3370,
% 3.23/1.00                 c_3759,c_6260,c_6280,c_6283]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7274,plain,
% 3.23/1.00      ( k1_funct_1(sK6,X0) = k1_funct_1(sK5,X0)
% 3.23/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_7251,c_2705]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5,plain,
% 3.23/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_13,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_521,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_522,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_521]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_523,plain,
% 3.23/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7345,plain,
% 3.23/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_7274,c_523]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7351,plain,
% 3.23/1.00      ( k1_xboole_0 = X0
% 3.23/1.00      | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2714,c_7345]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.23/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2716,plain,
% 3.23/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.23/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.23/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7507,plain,
% 3.23/1.00      ( k1_xboole_0 = X0
% 3.23/1.00      | r2_hidden(sK1(X0,k1_xboole_0),X1) = iProver_top
% 3.23/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_7351,c_2716]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7877,plain,
% 3.23/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_7507,c_7345]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7904,plain,
% 3.23/1.00      ( sK5 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_6319,c_7877]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3449,plain,
% 3.23/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2704,c_2711]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6268,plain,
% 3.23/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6261,c_3449]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6316,plain,
% 3.23/1.00      ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6268,c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7903,plain,
% 3.23/1.00      ( sK6 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_6316,c_7877]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2936,plain,
% 3.23/1.00      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2935]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,[status(thm)],[c_7904,c_7903,c_2936,c_396,c_26]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.009
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.009
% 3.23/1.00  total_time:                             0.226
% 3.23/1.00  num_of_symbols:                         51
% 3.23/1.00  num_of_terms:                           5674
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          0
% 3.23/1.00  num_of_split_atoms:                     0
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    29
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        0
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        0
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       137
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        124
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        5
% 3.23/1.00  pred_elim:                              2
% 3.23/1.00  pred_elim_cl:                           4
% 3.23/1.00  pred_elim_cycles:                       7
% 3.23/1.00  merged_defs:                            8
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          8
% 3.23/1.00  prep_cycles:                            4
% 3.23/1.00  pred_elim_time:                         0.026
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                28
% 3.23/1.00  conjectures:                            5
% 3.23/1.00  epr:                                    6
% 3.23/1.00  horn:                                   20
% 3.23/1.00  ground:                                 11
% 3.23/1.00  unary:                                  8
% 3.23/1.00  binary:                                 10
% 3.23/1.00  lits:                                   68
% 3.23/1.00  lits_eq:                                29
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                1
% 3.23/1.00  fd_pseudo_cond:                         4
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      29
% 3.23/1.00  prop_fast_solver_calls:                 1275
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    2362
% 3.23/1.00  prop_preprocess_simplified:             6798
% 3.23/1.00  prop_fo_subsumed:                       43
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.00  bmc1_unsat_core_size:                   -1
% 3.23/1.00  bmc1_unsat_core_parents_size:           -1
% 3.23/1.00  bmc1_merge_next_fun:                    0
% 3.23/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation
% 3.23/1.00  
% 3.23/1.00  inst_num_of_clauses:                    687
% 3.23/1.00  inst_num_in_passive:                    339
% 3.23/1.00  inst_num_in_active:                     322
% 3.23/1.00  inst_num_in_unprocessed:                26
% 3.23/1.00  inst_num_of_loops:                      500
% 3.23/1.00  inst_num_of_learning_restarts:          0
% 3.23/1.00  inst_num_moves_active_passive:          175
% 3.23/1.00  inst_lit_activity:                      0
% 3.23/1.00  inst_lit_activity_moves:                0
% 3.23/1.00  inst_num_tautologies:                   0
% 3.23/1.00  inst_num_prop_implied:                  0
% 3.23/1.00  inst_num_existing_simplified:           0
% 3.23/1.00  inst_num_eq_res_simplified:             0
% 3.23/1.00  inst_num_child_elim:                    0
% 3.23/1.00  inst_num_of_dismatching_blockings:      259
% 3.23/1.00  inst_num_of_non_proper_insts:           639
% 3.23/1.00  inst_num_of_duplicates:                 0
% 3.23/1.00  inst_inst_num_from_inst_to_res:         0
% 3.23/1.00  inst_dismatching_checking_time:         0.
% 3.23/1.00  
% 3.23/1.00  ------ Resolution
% 3.23/1.00  
% 3.23/1.00  res_num_of_clauses:                     0
% 3.23/1.00  res_num_in_passive:                     0
% 3.23/1.00  res_num_in_active:                      0
% 3.23/1.00  res_num_of_loops:                       141
% 3.23/1.00  res_forward_subset_subsumed:            69
% 3.23/1.00  res_backward_subset_subsumed:           0
% 3.23/1.00  res_forward_subsumed:                   0
% 3.23/1.00  res_backward_subsumed:                  1
% 3.23/1.00  res_forward_subsumption_resolution:     0
% 3.23/1.00  res_backward_subsumption_resolution:    1
% 3.23/1.00  res_clause_to_clause_subsumption:       444
% 3.23/1.00  res_orphan_elimination:                 0
% 3.23/1.00  res_tautology_del:                      68
% 3.23/1.00  res_num_eq_res_simplified:              0
% 3.23/1.00  res_num_sel_changes:                    0
% 3.23/1.00  res_moves_from_active_to_pass:          0
% 3.23/1.00  
% 3.23/1.00  ------ Superposition
% 3.23/1.00  
% 3.23/1.00  sup_time_total:                         0.
% 3.23/1.00  sup_time_generating:                    0.
% 3.23/1.00  sup_time_sim_full:                      0.
% 3.23/1.00  sup_time_sim_immed:                     0.
% 3.23/1.00  
% 3.23/1.00  sup_num_of_clauses:                     83
% 3.23/1.00  sup_num_in_active:                      57
% 3.23/1.00  sup_num_in_passive:                     26
% 3.23/1.00  sup_num_of_loops:                       99
% 3.23/1.00  sup_fw_superposition:                   84
% 3.23/1.00  sup_bw_superposition:                   71
% 3.23/1.00  sup_immediate_simplified:               27
% 3.23/1.00  sup_given_eliminated:                   0
% 3.23/1.00  comparisons_done:                       0
% 3.23/1.00  comparisons_avoided:                    47
% 3.23/1.00  
% 3.23/1.00  ------ Simplifications
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  sim_fw_subset_subsumed:                 10
% 3.23/1.00  sim_bw_subset_subsumed:                 12
% 3.23/1.00  sim_fw_subsumed:                        3
% 3.23/1.00  sim_bw_subsumed:                        1
% 3.23/1.00  sim_fw_subsumption_res:                 4
% 3.23/1.00  sim_bw_subsumption_res:                 0
% 3.23/1.00  sim_tautology_del:                      3
% 3.23/1.00  sim_eq_tautology_del:                   28
% 3.23/1.00  sim_eq_res_simp:                        2
% 3.23/1.00  sim_fw_demodulated:                     11
% 3.23/1.00  sim_bw_demodulated:                     36
% 3.23/1.00  sim_light_normalised:                   4
% 3.23/1.00  sim_joinable_taut:                      0
% 3.23/1.00  sim_joinable_simp:                      0
% 3.23/1.00  sim_ac_normalised:                      0
% 3.23/1.00  sim_smt_subsumption:                    0
% 3.23/1.00  
%------------------------------------------------------------------------------
