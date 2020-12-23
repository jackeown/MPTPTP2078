%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:47 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  222 (8901 expanded)
%              Number of clauses        :  157 (2758 expanded)
%              Number of leaves         :   19 (2260 expanded)
%              Depth                    :   39
%              Number of atoms          :  764 (46143 expanded)
%              Number of equality atoms :  466 (16860 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f18])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f41,f40])).

fof(f70,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f24])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f73,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_765,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_751,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3626,plain,
    ( k1_funct_1(sK6,sK7(sK1(X0,sK5))) = sK1(X0,sK5)
    | k2_relat_1(X0) = sK5
    | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_765,c_751])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_749,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_752,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1178,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_752])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1625,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_30])).

cnf(c_1626,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1625])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_759,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1908,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_749,c_759])).

cnf(c_2183,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1626,c_1908])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_747,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_766,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3873,plain,
    ( k1_funct_1(X0,sK2(X0,sK5)) = sK1(X0,sK5)
    | k1_funct_1(sK6,sK7(sK1(X0,sK5))) = sK1(X0,sK5)
    | k2_relat_1(X0) = sK5
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_751])).

cnf(c_4180,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_747,c_3873])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_758,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1904,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_749,c_758])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2096,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_1904,c_23])).

cnf(c_4181,plain,
    ( ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4180])).

cnf(c_4305,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4180,c_26,c_1011,c_2096,c_4181])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_764,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4309,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4305,c_764])).

cnf(c_29,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1012,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_5259,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4309,c_29,c_31,c_1012])).

cnf(c_5266,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_5259])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1126,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1513,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1516,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2247,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2260,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2261,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_270,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2870,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_2872,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_5870,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5266,c_28,c_29,c_26,c_31,c_4,c_1011,c_1012,c_1513,c_1516,c_2096,c_2247,c_2261,c_2872])).

cnf(c_5871,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5870])).

cnf(c_774,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5876,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5871,c_774])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_767,plain,
    ( sK1(X0,X1) != k1_funct_1(X0,X2)
    | k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4310,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4305,c_767])).

cnf(c_5406,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4310,c_29,c_31,c_1012])).

cnf(c_5417,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5406])).

cnf(c_5920,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5417,c_29,c_31,c_1012,c_1516,c_2096])).

cnf(c_5926,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_5920])).

cnf(c_5927,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5926])).

cnf(c_6210,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5876,c_28,c_26,c_4,c_1011,c_1513,c_2096,c_2247,c_2260,c_2872,c_5927])).

cnf(c_6217,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6210,c_764])).

cnf(c_10062,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6217,c_29,c_31,c_1012])).

cnf(c_10071,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_10062])).

cnf(c_10411,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10071,c_29,c_31,c_1012,c_2096])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_768,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_771,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2463,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_771])).

cnf(c_10421,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10411,c_2463])).

cnf(c_13282,plain,
    ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | v5_relat_1(sK6,X0) != iProver_top
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10421,c_31,c_1012])).

cnf(c_13283,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_13282])).

cnf(c_13297,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | v5_relat_1(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13283,c_751])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v5_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1037,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v5_relat_1(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_13425,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13297,c_31,c_1037])).

cnf(c_4729,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_764,c_2463])).

cnf(c_29818,plain,
    ( v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13425,c_4729])).

cnf(c_92,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2353,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2354,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_2356,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_2871,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2870])).

cnf(c_2873,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1428,plain,
    ( v5_relat_1(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_760])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_772,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4726,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | r2_hidden(sK0(k2_relat_1(X0),X2),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_2463])).

cnf(c_8205,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4726,c_774])).

cnf(c_8373,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_8205])).

cnf(c_8607,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8373,c_31,c_1012])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_769,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8616,plain,
    ( v5_relat_1(sK6,X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8607,c_769])).

cnf(c_8633,plain,
    ( v5_relat_1(sK6,k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8616])).

cnf(c_10072,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_10062])).

cnf(c_3624,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_765,c_774])).

cnf(c_11333,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3624,c_10062])).

cnf(c_11797,plain,
    ( r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10072,c_29,c_31,c_92,c_1012,c_2096,c_2873,c_11333])).

cnf(c_11808,plain,
    ( v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11797,c_2463])).

cnf(c_770,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3871,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_774])).

cnf(c_12754,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_747,c_3871])).

cnf(c_6528,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(sK6))
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_6529,plain,
    ( k2_relat_1(sK6) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6528])).

cnf(c_3623,plain,
    ( k2_relat_1(sK6) = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),sK4) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_765])).

cnf(c_10838,plain,
    ( k2_relat_1(sK6) = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),sK4) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3623,c_29,c_31,c_1012])).

cnf(c_750,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3595,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_764,c_774])).

cnf(c_6595,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_3595])).

cnf(c_1058,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1127,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1133,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_1135,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_268,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1053,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_1396,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1162,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_1673,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1674,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_3284,plain,
    ( ~ r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3285,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3284])).

cnf(c_3287,plain,
    ( r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,sK2(sK6,k1_xboole_0)),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3285])).

cnf(c_5110,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6))
    | ~ v1_xboole_0(k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5111,plain,
    ( r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5110])).

cnf(c_5113,plain,
    ( r2_hidden(k1_funct_1(sK6,sK2(sK6,k1_xboole_0)),k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5111])).

cnf(c_6995,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6595,c_29,c_26,c_31,c_23,c_92,c_1012,c_1058,c_1135,c_1396,c_1674,c_2356,c_3287,c_5113])).

cnf(c_7006,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_750,c_6995])).

cnf(c_10851,plain,
    ( k2_relat_1(sK6) = sK5
    | sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK4) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10838,c_7006])).

cnf(c_11616,plain,
    ( r2_hidden(sK2(sK6,sK5),sK4) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10851,c_29,c_26,c_31,c_23,c_92,c_1012,c_1058,c_1135,c_1396,c_1674,c_2096,c_2356,c_3287,c_5113])).

cnf(c_11622,plain,
    ( v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11616,c_6995])).

cnf(c_12802,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12754,c_31,c_1012,c_6529,c_11622])).

cnf(c_12810,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_770,c_12802])).

cnf(c_12812,plain,
    ( r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12810,c_764])).

cnf(c_6531,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | v1_xboole_0(k2_relat_1(sK6)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6529])).

cnf(c_12984,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12812,c_29,c_31,c_92,c_1012,c_1135,c_2356,c_6531,c_11622])).

cnf(c_12994,plain,
    ( v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12984,c_2463])).

cnf(c_13030,plain,
    ( v5_relat_1(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12994])).

cnf(c_13429,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13425,c_767])).

cnf(c_13977,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13429,c_29,c_31,c_1012])).

cnf(c_13985,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_13977])).

cnf(c_13988,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13985,c_2096])).

cnf(c_13994,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_13988])).

cnf(c_14144,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13994,c_31,c_92,c_1012,c_2261,c_2356,c_2873,c_8633,c_13030])).

cnf(c_14153,plain,
    ( k2_relat_1(sK6) = sK5
    | sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10838,c_14144])).

cnf(c_32648,plain,
    ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | v5_relat_1(sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29818,c_31,c_92,c_1012,c_2096,c_2356,c_2873,c_8633,c_11808,c_13030,c_14153])).

cnf(c_32649,plain,
    ( v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_32648])).

cnf(c_32684,plain,
    ( v5_relat_1(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_32649,c_14144])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32684,c_1037,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:13:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.00/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.49  
% 8.00/1.49  ------  iProver source info
% 8.00/1.49  
% 8.00/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.49  git: non_committed_changes: false
% 8.00/1.49  git: last_make_outside_of_git: false
% 8.00/1.49  
% 8.00/1.49  ------ 
% 8.00/1.49  ------ Parsing...
% 8.00/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.49  ------ Proving...
% 8.00/1.49  ------ Problem Properties 
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  clauses                                 29
% 8.00/1.49  conjectures                             6
% 8.00/1.49  EPR                                     5
% 8.00/1.49  Horn                                    22
% 8.00/1.49  unary                                   5
% 8.00/1.49  binary                                  9
% 8.00/1.49  lits                                    81
% 8.00/1.49  lits eq                                 19
% 8.00/1.49  fd_pure                                 0
% 8.00/1.49  fd_pseudo                               0
% 8.00/1.49  fd_cond                                 3
% 8.00/1.49  fd_pseudo_cond                          3
% 8.00/1.49  AC symbols                              0
% 8.00/1.49  
% 8.00/1.49  ------ Input Options Time Limit: Unbounded
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  ------ 
% 8.00/1.49  Current options:
% 8.00/1.49  ------ 
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  ------ Proving...
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  % SZS status Theorem for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  fof(f5,axiom,(
% 8.00/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f18,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f5])).
% 8.00/1.49  
% 8.00/1.49  fof(f19,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(flattening,[],[f18])).
% 8.00/1.49  
% 8.00/1.49  fof(f33,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(nnf_transformation,[],[f19])).
% 8.00/1.49  
% 8.00/1.49  fof(f34,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(rectify,[],[f33])).
% 8.00/1.49  
% 8.00/1.49  fof(f37,plain,(
% 8.00/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f36,plain,(
% 8.00/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f35,plain,(
% 8.00/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f38,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 8.00/1.49  
% 8.00/1.49  fof(f53,plain,(
% 8.00/1.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f11,conjecture,(
% 8.00/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f12,negated_conjecture,(
% 8.00/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 8.00/1.49    inference(negated_conjecture,[],[f11])).
% 8.00/1.49  
% 8.00/1.49  fof(f26,plain,(
% 8.00/1.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.00/1.49    inference(ennf_transformation,[],[f12])).
% 8.00/1.49  
% 8.00/1.49  fof(f27,plain,(
% 8.00/1.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.00/1.49    inference(flattening,[],[f26])).
% 8.00/1.49  
% 8.00/1.49  fof(f41,plain,(
% 8.00/1.49    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f40,plain,(
% 8.00/1.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f42,plain,(
% 8.00/1.49    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f41,f40])).
% 8.00/1.49  
% 8.00/1.49  fof(f70,plain,(
% 8.00/1.49    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f68,plain,(
% 8.00/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f10,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f24,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f10])).
% 8.00/1.49  
% 8.00/1.49  fof(f25,plain,(
% 8.00/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(flattening,[],[f24])).
% 8.00/1.49  
% 8.00/1.49  fof(f39,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(nnf_transformation,[],[f25])).
% 8.00/1.49  
% 8.00/1.49  fof(f60,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f39])).
% 8.00/1.49  
% 8.00/1.49  fof(f67,plain,(
% 8.00/1.49    v1_funct_2(sK6,sK4,sK5)),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f8,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f22,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f8])).
% 8.00/1.49  
% 8.00/1.49  fof(f58,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f22])).
% 8.00/1.49  
% 8.00/1.49  fof(f66,plain,(
% 8.00/1.49    v1_funct_1(sK6)),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f54,plain,(
% 8.00/1.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f6,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f20,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f6])).
% 8.00/1.49  
% 8.00/1.49  fof(f56,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f20])).
% 8.00/1.49  
% 8.00/1.49  fof(f9,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f23,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f9])).
% 8.00/1.49  
% 8.00/1.49  fof(f59,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f23])).
% 8.00/1.49  
% 8.00/1.49  fof(f71,plain,(
% 8.00/1.49    k2_relset_1(sK4,sK5,sK6) != sK5),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f52,plain,(
% 8.00/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f72,plain,(
% 8.00/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(equality_resolution,[],[f52])).
% 8.00/1.49  
% 8.00/1.49  fof(f73,plain,(
% 8.00/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(equality_resolution,[],[f72])).
% 8.00/1.49  
% 8.00/1.49  fof(f3,axiom,(
% 8.00/1.49    v1_xboole_0(k1_xboole_0)),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f47,plain,(
% 8.00/1.49    v1_xboole_0(k1_xboole_0)),
% 8.00/1.49    inference(cnf_transformation,[],[f3])).
% 8.00/1.49  
% 8.00/1.49  fof(f1,axiom,(
% 8.00/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f13,plain,(
% 8.00/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 8.00/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 8.00/1.49  
% 8.00/1.49  fof(f15,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 8.00/1.49    inference(ennf_transformation,[],[f13])).
% 8.00/1.49  
% 8.00/1.49  fof(f43,plain,(
% 8.00/1.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f15])).
% 8.00/1.49  
% 8.00/1.49  fof(f69,plain,(
% 8.00/1.49    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f55,plain,(
% 8.00/1.49    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f4,axiom,(
% 8.00/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f17,plain,(
% 8.00/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.00/1.49    inference(ennf_transformation,[],[f4])).
% 8.00/1.49  
% 8.00/1.49  fof(f32,plain,(
% 8.00/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.00/1.49    inference(nnf_transformation,[],[f17])).
% 8.00/1.49  
% 8.00/1.49  fof(f48,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f32])).
% 8.00/1.49  
% 8.00/1.49  fof(f2,axiom,(
% 8.00/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f16,plain,(
% 8.00/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f2])).
% 8.00/1.49  
% 8.00/1.49  fof(f28,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(nnf_transformation,[],[f16])).
% 8.00/1.49  
% 8.00/1.49  fof(f29,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(rectify,[],[f28])).
% 8.00/1.49  
% 8.00/1.49  fof(f30,plain,(
% 8.00/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f31,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 8.00/1.49  
% 8.00/1.49  fof(f44,plain,(
% 8.00/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f31])).
% 8.00/1.49  
% 8.00/1.49  fof(f7,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f14,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 8.00/1.49    inference(pure_predicate_removal,[],[f7])).
% 8.00/1.49  
% 8.00/1.49  fof(f21,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f14])).
% 8.00/1.49  
% 8.00/1.49  fof(f57,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f21])).
% 8.00/1.49  
% 8.00/1.49  fof(f45,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f31])).
% 8.00/1.49  
% 8.00/1.49  fof(f49,plain,(
% 8.00/1.49    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f32])).
% 8.00/1.49  
% 8.00/1.49  cnf(c_9,plain,
% 8.00/1.49      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 8.00/1.49      | r2_hidden(sK1(X0,X1),X1)
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | ~ v1_relat_1(X0)
% 8.00/1.49      | k2_relat_1(X0) = X1 ),
% 8.00/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_765,plain,
% 8.00/1.49      ( k2_relat_1(X0) = X1
% 8.00/1.49      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.00/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_24,negated_conjecture,
% 8.00/1.49      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 8.00/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_751,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3626,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(X0,sK5))) = sK1(X0,sK5)
% 8.00/1.49      | k2_relat_1(X0) = sK5
% 8.00/1.49      | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_765,c_751]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_26,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_749,plain,
% 8.00/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_22,plain,
% 8.00/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k1_relset_1(X1,X2,X0) = X1
% 8.00/1.49      | k1_xboole_0 = X2 ),
% 8.00/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_752,plain,
% 8.00/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 8.00/1.49      | k1_xboole_0 = X1
% 8.00/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1178,plain,
% 8.00/1.49      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_749,c_752]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27,negated_conjecture,
% 8.00/1.49      ( v1_funct_2(sK6,sK4,sK5) ),
% 8.00/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_30,plain,
% 8.00/1.49      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1625,plain,
% 8.00/1.49      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_1178,c_30]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1626,plain,
% 8.00/1.49      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_1625]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_15,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_759,plain,
% 8.00/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1908,plain,
% 8.00/1.49      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_749,c_759]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2183,plain,
% 8.00/1.49      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1626,c_1908]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_28,negated_conjecture,
% 8.00/1.49      ( v1_funct_1(sK6) ),
% 8.00/1.49      inference(cnf_transformation,[],[f66]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_747,plain,
% 8.00/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8,plain,
% 8.00/1.49      ( r2_hidden(sK1(X0,X1),X1)
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | ~ v1_relat_1(X0)
% 8.00/1.49      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 8.00/1.49      | k2_relat_1(X0) = X1 ),
% 8.00/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_766,plain,
% 8.00/1.49      ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 8.00/1.49      | k2_relat_1(X0) = X1
% 8.00/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3873,plain,
% 8.00/1.49      ( k1_funct_1(X0,sK2(X0,sK5)) = sK1(X0,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK7(sK1(X0,sK5))) = sK1(X0,sK5)
% 8.00/1.49      | k2_relat_1(X0) = sK5
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_766,c_751]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4180,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_747,c_3873]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | v1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1011,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 8.00/1.49      | v1_relat_1(sK6) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_16,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_758,plain,
% 8.00/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1904,plain,
% 8.00/1.49      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_749,c_758]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_23,negated_conjecture,
% 8.00/1.49      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 8.00/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2096,plain,
% 8.00/1.49      ( k2_relat_1(sK6) != sK5 ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_1904,c_23]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4181,plain,
% 8.00/1.49      ( ~ v1_relat_1(sK6)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5 ),
% 8.00/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4180]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4305,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4180,c_26,c_1011,c_2096,c_4181]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 8.00/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 8.00/1.49      | ~ v1_funct_1(X1)
% 8.00/1.49      | ~ v1_relat_1(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_764,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4309,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4305,c_764]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_29,plain,
% 8.00/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31,plain,
% 8.00/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1012,plain,
% 8.00/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5259,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4309,c_29,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5266,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_5259]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4,plain,
% 8.00/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1126,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,X0),X0)
% 8.00/1.49      | ~ v1_funct_1(sK6)
% 8.00/1.49      | ~ v1_relat_1(sK6)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 8.00/1.49      | k2_relat_1(sK6) = X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1513,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),sK5)
% 8.00/1.49      | ~ v1_funct_1(sK6)
% 8.00/1.49      | ~ v1_relat_1(sK6)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1126]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1516,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_0,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2247,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1(sK6,sK5),sK5) | ~ v1_xboole_0(sK5) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_25,negated_conjecture,
% 8.00/1.49      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 8.00/1.49      inference(cnf_transformation,[],[f69]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2260,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2261,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2260]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_270,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 8.00/1.49      theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2870,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_270]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2872,plain,
% 8.00/1.49      ( v1_xboole_0(sK5)
% 8.00/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 8.00/1.49      | sK5 != k1_xboole_0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2870]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5870,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_5266,c_28,c_29,c_26,c_31,c_4,c_1011,c_1012,c_1513,
% 8.00/1.49                 c_1516,c_2096,c_2247,c_2261,c_2872]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5871,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_5870]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_774,plain,
% 8.00/1.49      ( r2_hidden(X0,X1) != iProver_top
% 8.00/1.49      | v1_xboole_0(X1) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5876,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_5871,c_774]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 8.00/1.49      | ~ r2_hidden(sK1(X1,X2),X2)
% 8.00/1.49      | ~ v1_funct_1(X1)
% 8.00/1.49      | ~ v1_relat_1(X1)
% 8.00/1.49      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 8.00/1.49      | k2_relat_1(X1) = X2 ),
% 8.00/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_767,plain,
% 8.00/1.49      ( sK1(X0,X1) != k1_funct_1(X0,X2)
% 8.00/1.49      | k2_relat_1(X0) = X1
% 8.00/1.49      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(X0,X1),X1) != iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4310,plain,
% 8.00/1.49      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = X0
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4305,c_767]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5406,plain,
% 8.00/1.49      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = X0
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4310,c_29,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5417,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(equality_resolution,[status(thm)],[c_5406]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5920,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_5417,c_29,c_31,c_1012,c_1516,c_2096]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5926,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_5920]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5927,plain,
% 8.00/1.49      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 8.00/1.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 8.00/1.49      | sK5 = k1_xboole_0 ),
% 8.00/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5926]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6210,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_5876,c_28,c_26,c_4,c_1011,c_1513,c_2096,c_2247,c_2260,
% 8.00/1.49                 c_2872,c_5927]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6217,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_6210,c_764]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10062,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_6217,c_29,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10071,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = sK5
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3626,c_10062]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10411,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_10071,c_29,c_31,c_1012,c_2096]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6,plain,
% 8.00/1.49      ( ~ v5_relat_1(X0,X1)
% 8.00/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 8.00/1.49      | ~ v1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_768,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_771,plain,
% 8.00/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X0) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2463,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X1) = iProver_top
% 8.00/1.49      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_768,c_771]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10421,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_10411,c_2463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13282,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 8.00/1.49      | v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_10421,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13283,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_13282]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13297,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 8.00/1.49      | v5_relat_1(sK6,sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_13283,c_751]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_14,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | v5_relat_1(X0,X2) ),
% 8.00/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1036,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 8.00/1.49      | v5_relat_1(sK6,sK5) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1037,plain,
% 8.00/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 8.00/1.49      | v5_relat_1(sK6,sK5) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13425,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_13297,c_31,c_1037]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4729,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.00/1.49      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_764,c_2463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_29818,plain,
% 8.00/1.49      ( v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_13425,c_4729]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_92,plain,
% 8.00/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2353,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1(sK6,X0),X0) | ~ v1_xboole_0(X0) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2354,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2356,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 8.00/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2354]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2871,plain,
% 8.00/1.49      ( sK5 != X0
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2870]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2873,plain,
% 8.00/1.49      ( sK5 != k1_xboole_0
% 8.00/1.49      | v1_xboole_0(sK5) = iProver_top
% 8.00/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2871]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_760,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.00/1.49      | v5_relat_1(X0,X2) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1428,plain,
% 8.00/1.49      ( v5_relat_1(sK6,sK5) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_749,c_760]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2,plain,
% 8.00/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_772,plain,
% 8.00/1.49      ( r1_tarski(X0,X1) = iProver_top
% 8.00/1.49      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4726,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 8.00/1.49      | r2_hidden(sK0(k2_relat_1(X0),X2),X1) = iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_772,c_2463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8205,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(X1) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4726,c_774]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8373,plain,
% 8.00/1.49      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1428,c_8205]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8607,plain,
% 8.00/1.49      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_8373,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1)
% 8.00/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 8.00/1.49      | ~ v1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_769,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) = iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8616,plain,
% 8.00/1.49      ( v5_relat_1(sK6,X0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_8607,c_769]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8633,plain,
% 8.00/1.49      ( v5_relat_1(sK6,k1_xboole_0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_8616]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10072,plain,
% 8.00/1.49      ( sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_10062]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3624,plain,
% 8.00/1.49      ( k2_relat_1(X0) = X1
% 8.00/1.49      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(X1) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_765,c_774]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11333,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = sK5
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3624,c_10062]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11797,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_10072,c_29,c_31,c_92,c_1012,c_2096,c_2873,c_11333]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11808,plain,
% 8.00/1.49      ( v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK2(sK6,sK5),sK4) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_11797,c_2463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_770,plain,
% 8.00/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3871,plain,
% 8.00/1.49      ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 8.00/1.49      | k2_relat_1(X0) = X1
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(X1) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_766,c_774]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12754,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 8.00/1.49      | k2_relat_1(sK6) = X0
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_747,c_3871]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6528,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0)
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6))
% 8.00/1.49      | k2_relat_1(sK6) != X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_270]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6529,plain,
% 8.00/1.49      ( k2_relat_1(sK6) != X0
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_6528]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3623,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = X0
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,X0),sK4) = iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_765]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10838,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = X0
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,X0),sK4) = iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_3623,c_29,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_750,plain,
% 8.00/1.49      ( r2_hidden(X0,sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3595,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_764,c_774]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6595,plain,
% 8.00/1.49      ( sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(X0,sK4) != iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_3595]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1058,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 8.00/1.49      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1127,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0)
% 8.00/1.49      | ~ v1_funct_1(sK6)
% 8.00/1.49      | ~ v1_relat_1(sK6)
% 8.00/1.49      | k2_relat_1(sK6) = X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1133,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = X0
% 8.00/1.49      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1135,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1133]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_268,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1053,plain,
% 8.00/1.49      ( k2_relset_1(sK4,sK5,sK6) != X0
% 8.00/1.49      | k2_relset_1(sK4,sK5,sK6) = sK5
% 8.00/1.49      | sK5 != X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_268]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1396,plain,
% 8.00/1.49      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 8.00/1.49      | k2_relset_1(sK4,sK5,sK6) = sK5
% 8.00/1.49      | sK5 != k2_relat_1(sK6) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1162,plain,
% 8.00/1.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_268]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1673,plain,
% 8.00/1.49      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1162]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1674,plain,
% 8.00/1.49      ( k2_relat_1(sK6) != k1_xboole_0
% 8.00/1.49      | sK5 = k2_relat_1(sK6)
% 8.00/1.49      | sK5 != k1_xboole_0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1673]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3284,plain,
% 8.00/1.49      ( ~ r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 8.00/1.49      | r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6))
% 8.00/1.49      | ~ v1_funct_1(sK6)
% 8.00/1.49      | ~ v1_relat_1(sK6) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3285,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_3284]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3287,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(sK6,sK2(sK6,k1_xboole_0)),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_3285]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5110,plain,
% 8.00/1.49      ( ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6))
% 8.00/1.49      | ~ v1_xboole_0(k2_relat_1(sK6)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5111,plain,
% 8.00/1.49      ( r2_hidden(k1_funct_1(sK6,sK2(sK6,X0)),k2_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_5110]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5113,plain,
% 8.00/1.49      ( r2_hidden(k1_funct_1(sK6,sK2(sK6,k1_xboole_0)),k2_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_5111]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6995,plain,
% 8.00/1.49      ( r2_hidden(X0,sK4) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_6595,c_29,c_26,c_31,c_23,c_92,c_1012,c_1058,c_1135,
% 8.00/1.49                 c_1396,c_1674,c_2356,c_3287,c_5113]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7006,plain,
% 8.00/1.49      ( r2_hidden(X0,sK5) != iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_750,c_6995]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10851,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = sK5
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,sK5),sK4) = iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_10838,c_7006]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11616,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,sK5),sK4) = iProver_top
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_10851,c_29,c_26,c_31,c_23,c_92,c_1012,c_1058,c_1135,
% 8.00/1.49                 c_1396,c_1674,c_2096,c_2356,c_3287,c_5113]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11622,plain,
% 8.00/1.49      ( v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(forward_subsumption_resolution,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_11616,c_6995]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12802,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_12754,c_31,c_1012,c_6529,c_11622]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12810,plain,
% 8.00/1.49      ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_770,c_12802]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12812,plain,
% 8.00/1.49      ( r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_12810,c_764]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6531,plain,
% 8.00/1.49      ( k2_relat_1(sK6) != k1_xboole_0
% 8.00/1.49      | v1_xboole_0(k2_relat_1(sK6)) = iProver_top
% 8.00/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_6529]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12984,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_12812,c_29,c_31,c_92,c_1012,c_1135,c_2356,c_6531,
% 8.00/1.49                 c_11622]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12994,plain,
% 8.00/1.49      ( v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_12984,c_2463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13030,plain,
% 8.00/1.49      ( v5_relat_1(sK6,k1_xboole_0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_12994]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13429,plain,
% 8.00/1.49      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = X0
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK6) != iProver_top
% 8.00/1.49      | v1_relat_1(sK6) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_13425,c_767]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13977,plain,
% 8.00/1.49      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 8.00/1.49      | k2_relat_1(sK6) = X0
% 8.00/1.49      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_13429,c_29,c_31,c_1012]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13985,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = sK5
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(equality_resolution,[status(thm)],[c_13977]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13988,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_13985,c_2096]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13994,plain,
% 8.00/1.49      ( sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 8.00/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2183,c_13988]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_14144,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_13994,c_31,c_92,c_1012,c_2261,c_2356,c_2873,c_8633,
% 8.00/1.49                 c_13030]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_14153,plain,
% 8.00/1.49      ( k2_relat_1(sK6) = sK5
% 8.00/1.49      | sK5 = k1_xboole_0
% 8.00/1.49      | r2_hidden(sK2(sK6,sK5),sK4) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_10838,c_14144]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32648,plain,
% 8.00/1.49      ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 8.00/1.49      | v5_relat_1(sK6,X0) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_29818,c_31,c_92,c_1012,c_2096,c_2356,c_2873,c_8633,
% 8.00/1.49                 c_11808,c_13030,c_14153]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32649,plain,
% 8.00/1.49      ( v5_relat_1(sK6,X0) != iProver_top
% 8.00/1.49      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_32648]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32684,plain,
% 8.00/1.49      ( v5_relat_1(sK6,sK5) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_32649,c_14144]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(contradiction,plain,
% 8.00/1.49      ( $false ),
% 8.00/1.49      inference(minisat,[status(thm)],[c_32684,c_1037,c_31]) ).
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  ------                               Statistics
% 8.00/1.49  
% 8.00/1.49  ------ Selected
% 8.00/1.49  
% 8.00/1.49  total_time:                             0.972
% 8.00/1.49  
%------------------------------------------------------------------------------
