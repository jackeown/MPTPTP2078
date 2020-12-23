%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:59 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  194 (1575 expanded)
%              Number of clauses        :  119 ( 418 expanded)
%              Number of leaves         :   18 ( 465 expanded)
%              Depth                    :   23
%              Number of atoms          :  651 (11682 expanded)
%              Number of equality atoms :  268 (3811 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f49,f48,f47])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2662,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2669,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | k1_relset_1(X1,X2,X0) = X1
    | k1_relat_1(X3) != X1
    | k2_relat_1(X3) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_1231])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1236,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1232,c_21])).

cnf(c_2654,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_5535,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_2654])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_103,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5621,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5535,c_103])).

cnf(c_5622,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5621])).

cnf(c_5632,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2662,c_5622])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_475,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_476,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_478,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_32])).

cnf(c_2657,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2951,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2991,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2657,c_32,c_30,c_476,c_2951])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_461,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_462,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_464,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_32])).

cnf(c_2658,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_3189,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2658,c_32,c_30,c_462,c_2951])).

cnf(c_5636,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5632,c_2991,c_3189])).

cnf(c_5637,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5636,c_2991])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2952,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2951])).

cnf(c_2663,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_381,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_382,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_386,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_387,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_2688,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2663,c_382,c_387])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2666,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3187,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2688,c_2666])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2685,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_29,c_382,c_387])).

cnf(c_3466,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3187,c_2685])).

cnf(c_3675,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3466,c_2688])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_393,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_20,c_8,c_7])).

cnf(c_398,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_2660,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_4868,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3675,c_2660])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1290,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_1291,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1290])).

cnf(c_1293,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1291,c_32,c_30])).

cnf(c_2652,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_2691,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2652,c_382,c_387])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_368,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_369,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_371,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_33])).

cnf(c_2661,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_2694,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2691,c_2661])).

cnf(c_4967,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4868,c_2694])).

cnf(c_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_438,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_32])).

cnf(c_443,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_1470,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK1) != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_443])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1470])).

cnf(c_1473,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1471,c_30])).

cnf(c_2740,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1473,c_382,c_387,c_2685])).

cnf(c_2741,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2740])).

cnf(c_2819,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_27,c_382,c_387,c_2741])).

cnf(c_3677,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3466,c_2819])).

cnf(c_4975,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4967,c_3677])).

cnf(c_2664,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3574,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2991,c_2664])).

cnf(c_3587,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3574,c_3189])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2944,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2945,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2944])).

cnf(c_2947,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2948,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2947])).

cnf(c_4366,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_39,c_41,c_2945,c_2948,c_2952])).

cnf(c_4374,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4366,c_2666])).

cnf(c_4376,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4374,c_2991])).

cnf(c_4984,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4975,c_4376])).

cnf(c_4985,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_4984])).

cnf(c_5867,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5637,c_41,c_2952,c_4985])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2665,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4372,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4366,c_2665])).

cnf(c_3676,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3466,c_2661])).

cnf(c_19,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_413,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_414,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_424,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_414,c_7])).

cnf(c_2659,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_4168,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_2659])).

cnf(c_4191,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3189,c_4168])).

cnf(c_4695,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4372,c_39,c_41,c_2945,c_2948,c_2952,c_3676,c_4191])).

cnf(c_5878,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5867,c_4695])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_113,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5878,c_113])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.26/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.98  
% 3.26/0.98  ------  iProver source info
% 3.26/0.98  
% 3.26/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.98  git: non_committed_changes: false
% 3.26/0.98  git: last_make_outside_of_git: false
% 3.26/0.98  
% 3.26/0.98  ------ 
% 3.26/0.98  
% 3.26/0.98  ------ Input Options
% 3.26/0.98  
% 3.26/0.98  --out_options                           all
% 3.26/0.98  --tptp_safe_out                         true
% 3.26/0.98  --problem_path                          ""
% 3.26/0.98  --include_path                          ""
% 3.26/0.98  --clausifier                            res/vclausify_rel
% 3.26/0.98  --clausifier_options                    --mode clausify
% 3.26/0.98  --stdin                                 false
% 3.26/0.98  --stats_out                             all
% 3.26/0.98  
% 3.26/0.98  ------ General Options
% 3.26/0.98  
% 3.26/0.98  --fof                                   false
% 3.26/0.98  --time_out_real                         305.
% 3.26/0.98  --time_out_virtual                      -1.
% 3.26/0.98  --symbol_type_check                     false
% 3.26/0.98  --clausify_out                          false
% 3.26/0.98  --sig_cnt_out                           false
% 3.26/0.98  --trig_cnt_out                          false
% 3.26/0.98  --trig_cnt_out_tolerance                1.
% 3.26/0.98  --trig_cnt_out_sk_spl                   false
% 3.26/0.98  --abstr_cl_out                          false
% 3.26/0.98  
% 3.26/0.98  ------ Global Options
% 3.26/0.98  
% 3.26/0.98  --schedule                              default
% 3.26/0.98  --add_important_lit                     false
% 3.26/0.98  --prop_solver_per_cl                    1000
% 3.26/0.98  --min_unsat_core                        false
% 3.26/0.98  --soft_assumptions                      false
% 3.26/0.98  --soft_lemma_size                       3
% 3.26/0.98  --prop_impl_unit_size                   0
% 3.26/0.98  --prop_impl_unit                        []
% 3.26/0.98  --share_sel_clauses                     true
% 3.26/0.98  --reset_solvers                         false
% 3.26/0.98  --bc_imp_inh                            [conj_cone]
% 3.26/0.98  --conj_cone_tolerance                   3.
% 3.26/0.98  --extra_neg_conj                        none
% 3.26/0.98  --large_theory_mode                     true
% 3.26/0.98  --prolific_symb_bound                   200
% 3.26/0.98  --lt_threshold                          2000
% 3.26/0.98  --clause_weak_htbl                      true
% 3.26/0.98  --gc_record_bc_elim                     false
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing Options
% 3.26/0.98  
% 3.26/0.98  --preprocessing_flag                    true
% 3.26/0.98  --time_out_prep_mult                    0.1
% 3.26/0.98  --splitting_mode                        input
% 3.26/0.98  --splitting_grd                         true
% 3.26/0.98  --splitting_cvd                         false
% 3.26/0.98  --splitting_cvd_svl                     false
% 3.26/0.98  --splitting_nvd                         32
% 3.26/0.98  --sub_typing                            true
% 3.26/0.98  --prep_gs_sim                           true
% 3.26/0.98  --prep_unflatten                        true
% 3.26/0.98  --prep_res_sim                          true
% 3.26/0.98  --prep_upred                            true
% 3.26/0.98  --prep_sem_filter                       exhaustive
% 3.26/0.98  --prep_sem_filter_out                   false
% 3.26/0.98  --pred_elim                             true
% 3.26/0.98  --res_sim_input                         true
% 3.26/0.98  --eq_ax_congr_red                       true
% 3.26/0.98  --pure_diseq_elim                       true
% 3.26/0.98  --brand_transform                       false
% 3.26/0.98  --non_eq_to_eq                          false
% 3.26/0.98  --prep_def_merge                        true
% 3.26/0.98  --prep_def_merge_prop_impl              false
% 3.26/0.98  --prep_def_merge_mbd                    true
% 3.26/0.98  --prep_def_merge_tr_red                 false
% 3.26/0.98  --prep_def_merge_tr_cl                  false
% 3.26/0.98  --smt_preprocessing                     true
% 3.26/0.98  --smt_ac_axioms                         fast
% 3.26/0.98  --preprocessed_out                      false
% 3.26/0.98  --preprocessed_stats                    false
% 3.26/0.98  
% 3.26/0.98  ------ Abstraction refinement Options
% 3.26/0.98  
% 3.26/0.98  --abstr_ref                             []
% 3.26/0.98  --abstr_ref_prep                        false
% 3.26/0.98  --abstr_ref_until_sat                   false
% 3.26/0.98  --abstr_ref_sig_restrict                funpre
% 3.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.98  --abstr_ref_under                       []
% 3.26/0.98  
% 3.26/0.98  ------ SAT Options
% 3.26/0.98  
% 3.26/0.98  --sat_mode                              false
% 3.26/0.98  --sat_fm_restart_options                ""
% 3.26/0.98  --sat_gr_def                            false
% 3.26/0.98  --sat_epr_types                         true
% 3.26/0.98  --sat_non_cyclic_types                  false
% 3.26/0.98  --sat_finite_models                     false
% 3.26/0.98  --sat_fm_lemmas                         false
% 3.26/0.98  --sat_fm_prep                           false
% 3.26/0.98  --sat_fm_uc_incr                        true
% 3.26/0.98  --sat_out_model                         small
% 3.26/0.98  --sat_out_clauses                       false
% 3.26/0.98  
% 3.26/0.98  ------ QBF Options
% 3.26/0.98  
% 3.26/0.98  --qbf_mode                              false
% 3.26/0.98  --qbf_elim_univ                         false
% 3.26/0.98  --qbf_dom_inst                          none
% 3.26/0.98  --qbf_dom_pre_inst                      false
% 3.26/0.98  --qbf_sk_in                             false
% 3.26/0.98  --qbf_pred_elim                         true
% 3.26/0.98  --qbf_split                             512
% 3.26/0.98  
% 3.26/0.98  ------ BMC1 Options
% 3.26/0.98  
% 3.26/0.98  --bmc1_incremental                      false
% 3.26/0.98  --bmc1_axioms                           reachable_all
% 3.26/0.98  --bmc1_min_bound                        0
% 3.26/0.98  --bmc1_max_bound                        -1
% 3.26/0.98  --bmc1_max_bound_default                -1
% 3.26/0.98  --bmc1_symbol_reachability              true
% 3.26/0.98  --bmc1_property_lemmas                  false
% 3.26/0.98  --bmc1_k_induction                      false
% 3.26/0.98  --bmc1_non_equiv_states                 false
% 3.26/0.98  --bmc1_deadlock                         false
% 3.26/0.98  --bmc1_ucm                              false
% 3.26/0.98  --bmc1_add_unsat_core                   none
% 3.26/0.98  --bmc1_unsat_core_children              false
% 3.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.98  --bmc1_out_stat                         full
% 3.26/0.98  --bmc1_ground_init                      false
% 3.26/0.98  --bmc1_pre_inst_next_state              false
% 3.26/0.98  --bmc1_pre_inst_state                   false
% 3.26/0.98  --bmc1_pre_inst_reach_state             false
% 3.26/0.98  --bmc1_out_unsat_core                   false
% 3.26/0.98  --bmc1_aig_witness_out                  false
% 3.26/0.98  --bmc1_verbose                          false
% 3.26/0.98  --bmc1_dump_clauses_tptp                false
% 3.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.98  --bmc1_dump_file                        -
% 3.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.98  --bmc1_ucm_extend_mode                  1
% 3.26/0.98  --bmc1_ucm_init_mode                    2
% 3.26/0.98  --bmc1_ucm_cone_mode                    none
% 3.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.98  --bmc1_ucm_relax_model                  4
% 3.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.98  --bmc1_ucm_layered_model                none
% 3.26/0.98  --bmc1_ucm_max_lemma_size               10
% 3.26/0.98  
% 3.26/0.98  ------ AIG Options
% 3.26/0.98  
% 3.26/0.98  --aig_mode                              false
% 3.26/0.98  
% 3.26/0.98  ------ Instantiation Options
% 3.26/0.98  
% 3.26/0.98  --instantiation_flag                    true
% 3.26/0.98  --inst_sos_flag                         false
% 3.26/0.98  --inst_sos_phase                        true
% 3.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.98  --inst_lit_sel_side                     num_symb
% 3.26/0.98  --inst_solver_per_active                1400
% 3.26/0.98  --inst_solver_calls_frac                1.
% 3.26/0.98  --inst_passive_queue_type               priority_queues
% 3.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.98  --inst_passive_queues_freq              [25;2]
% 3.26/0.98  --inst_dismatching                      true
% 3.26/0.98  --inst_eager_unprocessed_to_passive     true
% 3.26/0.98  --inst_prop_sim_given                   true
% 3.26/0.98  --inst_prop_sim_new                     false
% 3.26/0.98  --inst_subs_new                         false
% 3.26/0.98  --inst_eq_res_simp                      false
% 3.26/0.98  --inst_subs_given                       false
% 3.26/0.98  --inst_orphan_elimination               true
% 3.26/0.98  --inst_learning_loop_flag               true
% 3.26/0.98  --inst_learning_start                   3000
% 3.26/0.98  --inst_learning_factor                  2
% 3.26/0.98  --inst_start_prop_sim_after_learn       3
% 3.26/0.98  --inst_sel_renew                        solver
% 3.26/0.98  --inst_lit_activity_flag                true
% 3.26/0.98  --inst_restr_to_given                   false
% 3.26/0.98  --inst_activity_threshold               500
% 3.26/0.98  --inst_out_proof                        true
% 3.26/0.98  
% 3.26/0.98  ------ Resolution Options
% 3.26/0.98  
% 3.26/0.98  --resolution_flag                       true
% 3.26/0.98  --res_lit_sel                           adaptive
% 3.26/0.98  --res_lit_sel_side                      none
% 3.26/0.98  --res_ordering                          kbo
% 3.26/0.98  --res_to_prop_solver                    active
% 3.26/0.98  --res_prop_simpl_new                    false
% 3.26/0.98  --res_prop_simpl_given                  true
% 3.26/0.98  --res_passive_queue_type                priority_queues
% 3.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.98  --res_passive_queues_freq               [15;5]
% 3.26/0.98  --res_forward_subs                      full
% 3.26/0.98  --res_backward_subs                     full
% 3.26/0.98  --res_forward_subs_resolution           true
% 3.26/0.98  --res_backward_subs_resolution          true
% 3.26/0.98  --res_orphan_elimination                true
% 3.26/0.98  --res_time_limit                        2.
% 3.26/0.98  --res_out_proof                         true
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Options
% 3.26/0.98  
% 3.26/0.98  --superposition_flag                    true
% 3.26/0.98  --sup_passive_queue_type                priority_queues
% 3.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.98  --demod_completeness_check              fast
% 3.26/0.98  --demod_use_ground                      true
% 3.26/0.98  --sup_to_prop_solver                    passive
% 3.26/0.98  --sup_prop_simpl_new                    true
% 3.26/0.98  --sup_prop_simpl_given                  true
% 3.26/0.98  --sup_fun_splitting                     false
% 3.26/0.98  --sup_smt_interval                      50000
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Simplification Setup
% 3.26/0.98  
% 3.26/0.98  --sup_indices_passive                   []
% 3.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_full_bw                           [BwDemod]
% 3.26/0.98  --sup_immed_triv                        [TrivRules]
% 3.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_immed_bw_main                     []
% 3.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  
% 3.26/0.98  ------ Combination Options
% 3.26/0.98  
% 3.26/0.98  --comb_res_mult                         3
% 3.26/0.98  --comb_sup_mult                         2
% 3.26/0.98  --comb_inst_mult                        10
% 3.26/0.98  
% 3.26/0.98  ------ Debug Options
% 3.26/0.98  
% 3.26/0.98  --dbg_backtrace                         false
% 3.26/0.98  --dbg_dump_prop_clauses                 false
% 3.26/0.98  --dbg_dump_prop_clauses_file            -
% 3.26/0.98  --dbg_out_stat                          false
% 3.26/0.98  ------ Parsing...
% 3.26/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.98  ------ Proving...
% 3.26/0.98  ------ Problem Properties 
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  clauses                                 35
% 3.26/0.98  conjectures                             4
% 3.26/0.98  EPR                                     2
% 3.26/0.98  Horn                                    25
% 3.26/0.98  unary                                   8
% 3.26/0.98  binary                                  10
% 3.26/0.98  lits                                    97
% 3.26/0.98  lits eq                                 40
% 3.26/0.98  fd_pure                                 0
% 3.26/0.98  fd_pseudo                               0
% 3.26/0.98  fd_cond                                 4
% 3.26/0.98  fd_pseudo_cond                          1
% 3.26/0.98  AC symbols                              0
% 3.26/0.98  
% 3.26/0.98  ------ Schedule dynamic 5 is on 
% 3.26/0.98  
% 3.26/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  ------ 
% 3.26/0.98  Current options:
% 3.26/0.98  ------ 
% 3.26/0.98  
% 3.26/0.98  ------ Input Options
% 3.26/0.98  
% 3.26/0.98  --out_options                           all
% 3.26/0.98  --tptp_safe_out                         true
% 3.26/0.98  --problem_path                          ""
% 3.26/0.98  --include_path                          ""
% 3.26/0.98  --clausifier                            res/vclausify_rel
% 3.26/0.98  --clausifier_options                    --mode clausify
% 3.26/0.98  --stdin                                 false
% 3.26/0.98  --stats_out                             all
% 3.26/0.98  
% 3.26/0.98  ------ General Options
% 3.26/0.98  
% 3.26/0.98  --fof                                   false
% 3.26/0.98  --time_out_real                         305.
% 3.26/0.98  --time_out_virtual                      -1.
% 3.26/0.98  --symbol_type_check                     false
% 3.26/0.98  --clausify_out                          false
% 3.26/0.98  --sig_cnt_out                           false
% 3.26/0.98  --trig_cnt_out                          false
% 3.26/0.98  --trig_cnt_out_tolerance                1.
% 3.26/0.98  --trig_cnt_out_sk_spl                   false
% 3.26/0.98  --abstr_cl_out                          false
% 3.26/0.98  
% 3.26/0.98  ------ Global Options
% 3.26/0.98  
% 3.26/0.98  --schedule                              default
% 3.26/0.98  --add_important_lit                     false
% 3.26/0.98  --prop_solver_per_cl                    1000
% 3.26/0.98  --min_unsat_core                        false
% 3.26/0.98  --soft_assumptions                      false
% 3.26/0.98  --soft_lemma_size                       3
% 3.26/0.98  --prop_impl_unit_size                   0
% 3.26/0.98  --prop_impl_unit                        []
% 3.26/0.98  --share_sel_clauses                     true
% 3.26/0.98  --reset_solvers                         false
% 3.26/0.98  --bc_imp_inh                            [conj_cone]
% 3.26/0.98  --conj_cone_tolerance                   3.
% 3.26/0.98  --extra_neg_conj                        none
% 3.26/0.98  --large_theory_mode                     true
% 3.26/0.98  --prolific_symb_bound                   200
% 3.26/0.98  --lt_threshold                          2000
% 3.26/0.98  --clause_weak_htbl                      true
% 3.26/0.98  --gc_record_bc_elim                     false
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing Options
% 3.26/0.98  
% 3.26/0.98  --preprocessing_flag                    true
% 3.26/0.98  --time_out_prep_mult                    0.1
% 3.26/0.98  --splitting_mode                        input
% 3.26/0.98  --splitting_grd                         true
% 3.26/0.98  --splitting_cvd                         false
% 3.26/0.98  --splitting_cvd_svl                     false
% 3.26/0.98  --splitting_nvd                         32
% 3.26/0.98  --sub_typing                            true
% 3.26/0.98  --prep_gs_sim                           true
% 3.26/0.98  --prep_unflatten                        true
% 3.26/0.98  --prep_res_sim                          true
% 3.26/0.98  --prep_upred                            true
% 3.26/0.98  --prep_sem_filter                       exhaustive
% 3.26/0.98  --prep_sem_filter_out                   false
% 3.26/0.98  --pred_elim                             true
% 3.26/0.98  --res_sim_input                         true
% 3.26/0.98  --eq_ax_congr_red                       true
% 3.26/0.98  --pure_diseq_elim                       true
% 3.26/0.98  --brand_transform                       false
% 3.26/0.98  --non_eq_to_eq                          false
% 3.26/0.98  --prep_def_merge                        true
% 3.26/0.98  --prep_def_merge_prop_impl              false
% 3.26/0.98  --prep_def_merge_mbd                    true
% 3.26/0.98  --prep_def_merge_tr_red                 false
% 3.26/0.98  --prep_def_merge_tr_cl                  false
% 3.26/0.98  --smt_preprocessing                     true
% 3.26/0.98  --smt_ac_axioms                         fast
% 3.26/0.98  --preprocessed_out                      false
% 3.26/0.98  --preprocessed_stats                    false
% 3.26/0.98  
% 3.26/0.98  ------ Abstraction refinement Options
% 3.26/0.98  
% 3.26/0.98  --abstr_ref                             []
% 3.26/0.98  --abstr_ref_prep                        false
% 3.26/0.98  --abstr_ref_until_sat                   false
% 3.26/0.98  --abstr_ref_sig_restrict                funpre
% 3.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.98  --abstr_ref_under                       []
% 3.26/0.98  
% 3.26/0.98  ------ SAT Options
% 3.26/0.98  
% 3.26/0.98  --sat_mode                              false
% 3.26/0.98  --sat_fm_restart_options                ""
% 3.26/0.98  --sat_gr_def                            false
% 3.26/0.98  --sat_epr_types                         true
% 3.26/0.98  --sat_non_cyclic_types                  false
% 3.26/0.98  --sat_finite_models                     false
% 3.26/0.98  --sat_fm_lemmas                         false
% 3.26/0.98  --sat_fm_prep                           false
% 3.26/0.98  --sat_fm_uc_incr                        true
% 3.26/0.98  --sat_out_model                         small
% 3.26/0.98  --sat_out_clauses                       false
% 3.26/0.98  
% 3.26/0.98  ------ QBF Options
% 3.26/0.98  
% 3.26/0.98  --qbf_mode                              false
% 3.26/0.98  --qbf_elim_univ                         false
% 3.26/0.98  --qbf_dom_inst                          none
% 3.26/0.98  --qbf_dom_pre_inst                      false
% 3.26/0.98  --qbf_sk_in                             false
% 3.26/0.98  --qbf_pred_elim                         true
% 3.26/0.98  --qbf_split                             512
% 3.26/0.98  
% 3.26/0.98  ------ BMC1 Options
% 3.26/0.98  
% 3.26/0.98  --bmc1_incremental                      false
% 3.26/0.98  --bmc1_axioms                           reachable_all
% 3.26/0.98  --bmc1_min_bound                        0
% 3.26/0.98  --bmc1_max_bound                        -1
% 3.26/0.98  --bmc1_max_bound_default                -1
% 3.26/0.98  --bmc1_symbol_reachability              true
% 3.26/0.98  --bmc1_property_lemmas                  false
% 3.26/0.98  --bmc1_k_induction                      false
% 3.26/0.98  --bmc1_non_equiv_states                 false
% 3.26/0.98  --bmc1_deadlock                         false
% 3.26/0.98  --bmc1_ucm                              false
% 3.26/0.98  --bmc1_add_unsat_core                   none
% 3.26/0.98  --bmc1_unsat_core_children              false
% 3.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.98  --bmc1_out_stat                         full
% 3.26/0.98  --bmc1_ground_init                      false
% 3.26/0.98  --bmc1_pre_inst_next_state              false
% 3.26/0.98  --bmc1_pre_inst_state                   false
% 3.26/0.98  --bmc1_pre_inst_reach_state             false
% 3.26/0.98  --bmc1_out_unsat_core                   false
% 3.26/0.98  --bmc1_aig_witness_out                  false
% 3.26/0.98  --bmc1_verbose                          false
% 3.26/0.98  --bmc1_dump_clauses_tptp                false
% 3.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.98  --bmc1_dump_file                        -
% 3.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.98  --bmc1_ucm_extend_mode                  1
% 3.26/0.98  --bmc1_ucm_init_mode                    2
% 3.26/0.98  --bmc1_ucm_cone_mode                    none
% 3.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.98  --bmc1_ucm_relax_model                  4
% 3.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.98  --bmc1_ucm_layered_model                none
% 3.26/0.98  --bmc1_ucm_max_lemma_size               10
% 3.26/0.98  
% 3.26/0.98  ------ AIG Options
% 3.26/0.98  
% 3.26/0.98  --aig_mode                              false
% 3.26/0.98  
% 3.26/0.98  ------ Instantiation Options
% 3.26/0.98  
% 3.26/0.98  --instantiation_flag                    true
% 3.26/0.98  --inst_sos_flag                         false
% 3.26/0.98  --inst_sos_phase                        true
% 3.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.98  --inst_lit_sel_side                     none
% 3.26/0.98  --inst_solver_per_active                1400
% 3.26/0.98  --inst_solver_calls_frac                1.
% 3.26/0.98  --inst_passive_queue_type               priority_queues
% 3.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.98  --inst_passive_queues_freq              [25;2]
% 3.26/0.98  --inst_dismatching                      true
% 3.26/0.98  --inst_eager_unprocessed_to_passive     true
% 3.26/0.98  --inst_prop_sim_given                   true
% 3.26/0.98  --inst_prop_sim_new                     false
% 3.26/0.98  --inst_subs_new                         false
% 3.26/0.98  --inst_eq_res_simp                      false
% 3.26/0.98  --inst_subs_given                       false
% 3.26/0.98  --inst_orphan_elimination               true
% 3.26/0.98  --inst_learning_loop_flag               true
% 3.26/0.98  --inst_learning_start                   3000
% 3.26/0.98  --inst_learning_factor                  2
% 3.26/0.98  --inst_start_prop_sim_after_learn       3
% 3.26/0.98  --inst_sel_renew                        solver
% 3.26/0.98  --inst_lit_activity_flag                true
% 3.26/0.98  --inst_restr_to_given                   false
% 3.26/0.98  --inst_activity_threshold               500
% 3.26/0.98  --inst_out_proof                        true
% 3.26/0.98  
% 3.26/0.98  ------ Resolution Options
% 3.26/0.98  
% 3.26/0.98  --resolution_flag                       false
% 3.26/0.98  --res_lit_sel                           adaptive
% 3.26/0.98  --res_lit_sel_side                      none
% 3.26/0.98  --res_ordering                          kbo
% 3.26/0.98  --res_to_prop_solver                    active
% 3.26/0.98  --res_prop_simpl_new                    false
% 3.26/0.98  --res_prop_simpl_given                  true
% 3.26/0.98  --res_passive_queue_type                priority_queues
% 3.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.98  --res_passive_queues_freq               [15;5]
% 3.26/0.98  --res_forward_subs                      full
% 3.26/0.98  --res_backward_subs                     full
% 3.26/0.98  --res_forward_subs_resolution           true
% 3.26/0.98  --res_backward_subs_resolution          true
% 3.26/0.98  --res_orphan_elimination                true
% 3.26/0.98  --res_time_limit                        2.
% 3.26/0.98  --res_out_proof                         true
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Options
% 3.26/0.98  
% 3.26/0.98  --superposition_flag                    true
% 3.26/0.98  --sup_passive_queue_type                priority_queues
% 3.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.98  --demod_completeness_check              fast
% 3.26/0.98  --demod_use_ground                      true
% 3.26/0.98  --sup_to_prop_solver                    passive
% 3.26/0.98  --sup_prop_simpl_new                    true
% 3.26/0.98  --sup_prop_simpl_given                  true
% 3.26/0.98  --sup_fun_splitting                     false
% 3.26/0.98  --sup_smt_interval                      50000
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Simplification Setup
% 3.26/0.98  
% 3.26/0.98  --sup_indices_passive                   []
% 3.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_full_bw                           [BwDemod]
% 3.26/0.98  --sup_immed_triv                        [TrivRules]
% 3.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_immed_bw_main                     []
% 3.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  
% 3.26/0.98  ------ Combination Options
% 3.26/0.98  
% 3.26/0.98  --comb_res_mult                         3
% 3.26/0.98  --comb_sup_mult                         2
% 3.26/0.98  --comb_inst_mult                        10
% 3.26/0.98  
% 3.26/0.98  ------ Debug Options
% 3.26/0.98  
% 3.26/0.98  --dbg_backtrace                         false
% 3.26/0.98  --dbg_dump_prop_clauses                 false
% 3.26/0.98  --dbg_dump_prop_clauses_file            -
% 3.26/0.98  --dbg_out_stat                          false
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  ------ Proving...
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  % SZS status Theorem for theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  fof(f17,conjecture,(
% 3.26/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f18,negated_conjecture,(
% 3.26/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.26/0.98    inference(negated_conjecture,[],[f17])).
% 3.26/0.98  
% 3.26/0.98  fof(f43,plain,(
% 3.26/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f18])).
% 3.26/0.98  
% 3.26/0.98  fof(f44,plain,(
% 3.26/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.26/0.98    inference(flattening,[],[f43])).
% 3.26/0.98  
% 3.26/0.98  fof(f49,plain,(
% 3.26/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.26/0.98    introduced(choice_axiom,[])).
% 3.26/0.98  
% 3.26/0.98  fof(f48,plain,(
% 3.26/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.26/0.98    introduced(choice_axiom,[])).
% 3.26/0.98  
% 3.26/0.98  fof(f47,plain,(
% 3.26/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.26/0.98    introduced(choice_axiom,[])).
% 3.26/0.98  
% 3.26/0.98  fof(f50,plain,(
% 3.26/0.98    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f49,f48,f47])).
% 3.26/0.98  
% 3.26/0.98  fof(f81,plain,(
% 3.26/0.98    v1_funct_1(sK2)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f4,axiom,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f21,plain,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f4])).
% 3.26/0.98  
% 3.26/0.98  fof(f22,plain,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f21])).
% 3.26/0.98  
% 3.26/0.98  fof(f55,plain,(
% 3.26/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f22])).
% 3.26/0.98  
% 3.26/0.98  fof(f11,axiom,(
% 3.26/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f32,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(ennf_transformation,[],[f11])).
% 3.26/0.98  
% 3.26/0.98  fof(f33,plain,(
% 3.26/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(flattening,[],[f32])).
% 3.26/0.98  
% 3.26/0.98  fof(f45,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(nnf_transformation,[],[f33])).
% 3.26/0.98  
% 3.26/0.98  fof(f64,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.98    inference(cnf_transformation,[],[f45])).
% 3.26/0.98  
% 3.26/0.98  fof(f13,axiom,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f36,plain,(
% 3.26/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f13])).
% 3.26/0.98  
% 3.26/0.98  fof(f37,plain,(
% 3.26/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f36])).
% 3.26/0.98  
% 3.26/0.98  fof(f73,plain,(
% 3.26/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f37])).
% 3.26/0.98  
% 3.26/0.98  fof(f74,plain,(
% 3.26/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f37])).
% 3.26/0.98  
% 3.26/0.98  fof(f54,plain,(
% 3.26/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f22])).
% 3.26/0.98  
% 3.26/0.98  fof(f5,axiom,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f23,plain,(
% 3.26/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f5])).
% 3.26/0.98  
% 3.26/0.98  fof(f24,plain,(
% 3.26/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f23])).
% 3.26/0.98  
% 3.26/0.98  fof(f57,plain,(
% 3.26/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  fof(f85,plain,(
% 3.26/0.98    v2_funct_1(sK2)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f83,plain,(
% 3.26/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f6,axiom,(
% 3.26/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f25,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(ennf_transformation,[],[f6])).
% 3.26/0.98  
% 3.26/0.98  fof(f58,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.98    inference(cnf_transformation,[],[f25])).
% 3.26/0.98  
% 3.26/0.98  fof(f56,plain,(
% 3.26/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  fof(f14,axiom,(
% 3.26/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f38,plain,(
% 3.26/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f14])).
% 3.26/0.98  
% 3.26/0.98  fof(f75,plain,(
% 3.26/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f38])).
% 3.26/0.98  
% 3.26/0.98  fof(f80,plain,(
% 3.26/0.98    l1_struct_0(sK1)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f78,plain,(
% 3.26/0.98    l1_struct_0(sK0)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f8,axiom,(
% 3.26/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f27,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(ennf_transformation,[],[f8])).
% 3.26/0.98  
% 3.26/0.98  fof(f60,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.98    inference(cnf_transformation,[],[f27])).
% 3.26/0.98  
% 3.26/0.98  fof(f84,plain,(
% 3.26/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f7,axiom,(
% 3.26/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f19,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.26/0.98    inference(pure_predicate_removal,[],[f7])).
% 3.26/0.98  
% 3.26/0.98  fof(f26,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.98    inference(ennf_transformation,[],[f19])).
% 3.26/0.98  
% 3.26/0.98  fof(f59,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.98    inference(cnf_transformation,[],[f26])).
% 3.26/0.98  
% 3.26/0.98  fof(f12,axiom,(
% 3.26/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f34,plain,(
% 3.26/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.26/0.98    inference(ennf_transformation,[],[f12])).
% 3.26/0.98  
% 3.26/0.98  fof(f35,plain,(
% 3.26/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.26/0.98    inference(flattening,[],[f34])).
% 3.26/0.98  
% 3.26/0.98  fof(f46,plain,(
% 3.26/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.26/0.98    inference(nnf_transformation,[],[f35])).
% 3.26/0.98  
% 3.26/0.98  fof(f70,plain,(
% 3.26/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f46])).
% 3.26/0.98  
% 3.26/0.98  fof(f10,axiom,(
% 3.26/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f30,plain,(
% 3.26/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.26/0.98    inference(ennf_transformation,[],[f10])).
% 3.26/0.98  
% 3.26/0.98  fof(f31,plain,(
% 3.26/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.26/0.98    inference(flattening,[],[f30])).
% 3.26/0.98  
% 3.26/0.98  fof(f63,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f31])).
% 3.26/0.98  
% 3.26/0.98  fof(f82,plain,(
% 3.26/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f15,axiom,(
% 3.26/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f39,plain,(
% 3.26/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f15])).
% 3.26/0.98  
% 3.26/0.98  fof(f40,plain,(
% 3.26/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/0.98    inference(flattening,[],[f39])).
% 3.26/0.98  
% 3.26/0.98  fof(f76,plain,(
% 3.26/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f40])).
% 3.26/0.98  
% 3.26/0.98  fof(f79,plain,(
% 3.26/0.98    ~v2_struct_0(sK1)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f86,plain,(
% 3.26/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 3.26/0.98    inference(cnf_transformation,[],[f50])).
% 3.26/0.98  
% 3.26/0.98  fof(f16,axiom,(
% 3.26/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f41,plain,(
% 3.26/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.26/0.98    inference(ennf_transformation,[],[f16])).
% 3.26/0.98  
% 3.26/0.98  fof(f42,plain,(
% 3.26/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.26/0.98    inference(flattening,[],[f41])).
% 3.26/0.98  
% 3.26/0.98  fof(f77,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f42])).
% 3.26/0.98  
% 3.26/0.98  fof(f9,axiom,(
% 3.26/0.98    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f28,plain,(
% 3.26/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f9])).
% 3.26/0.98  
% 3.26/0.98  fof(f29,plain,(
% 3.26/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.26/0.98    inference(flattening,[],[f28])).
% 3.26/0.98  
% 3.26/0.98  fof(f61,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f29])).
% 3.26/0.98  
% 3.26/0.98  fof(f71,plain,(
% 3.26/0.98    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f46])).
% 3.26/0.98  
% 3.26/0.98  fof(f92,plain,(
% 3.26/0.98    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.26/0.98    inference(equality_resolution,[],[f71])).
% 3.26/0.98  
% 3.26/0.98  fof(f1,axiom,(
% 3.26/0.98    v1_xboole_0(k1_xboole_0)),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f51,plain,(
% 3.26/0.98    v1_xboole_0(k1_xboole_0)),
% 3.26/0.98    inference(cnf_transformation,[],[f1])).
% 3.26/0.98  
% 3.26/0.98  cnf(c_32,negated_conjecture,
% 3.26/0.98      ( v1_funct_1(sK2) ),
% 3.26/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2662,plain,
% 3.26/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | v1_funct_1(k2_funct_1(X0))
% 3.26/0.98      | ~ v1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2669,plain,
% 3.26/0.98      ( v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_18,plain,
% 3.26/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.26/0.98      | k1_xboole_0 = X2 ),
% 3.26/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_22,plain,
% 3.26/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1231,plain,
% 3.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | ~ v1_funct_1(X3)
% 3.26/0.98      | ~ v1_relat_1(X3)
% 3.26/0.98      | X3 != X0
% 3.26/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.26/0.98      | k1_relat_1(X3) != X1
% 3.26/0.98      | k2_relat_1(X3) != X2
% 3.26/0.98      | k1_xboole_0 = X2 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1232,plain,
% 3.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/0.98      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_1231]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_21,plain,
% 3.26/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1236,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/0.98      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_1232,c_21]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2654,plain,
% 3.26/0.98      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/0.98      | k1_xboole_0 = k2_relat_1(X0)
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5535,plain,
% 3.26/0.98      ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_2669,c_2654]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_4,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_103,plain,
% 3.26/0.98      ( v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5621,plain,
% 3.26/0.98      ( v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 3.26/0.98      | k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0)) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_5535,c_103]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5622,plain,
% 3.26/0.98      ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(renaming,[status(thm)],[c_5621]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5632,plain,
% 3.26/0.98      ( k1_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.26/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_2662,c_5622]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5,plain,
% 3.26/0.98      ( ~ v2_funct_1(X0)
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_28,negated_conjecture,
% 3.26/0.98      ( v2_funct_1(sK2) ),
% 3.26/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_475,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.26/0.98      | sK2 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_476,plain,
% 3.26/0.98      ( ~ v1_funct_1(sK2)
% 3.26/0.98      | ~ v1_relat_1(sK2)
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_475]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_478,plain,
% 3.26/0.98      ( ~ v1_relat_1(sK2)
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_476,c_32]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2657,plain,
% 3.26/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.26/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_30,negated_conjecture,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.26/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7,plain,
% 3.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | v1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2951,plain,
% 3.26/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.26/0.98      | v1_relat_1(sK2) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2991,plain,
% 3.26/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_2657,c_32,c_30,c_476,c_2951]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_6,plain,
% 3.26/0.98      ( ~ v2_funct_1(X0)
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_461,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.26/0.98      | sK2 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_462,plain,
% 3.26/0.98      ( ~ v1_funct_1(sK2)
% 3.26/0.98      | ~ v1_relat_1(sK2)
% 3.26/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_461]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_464,plain,
% 3.26/0.98      ( ~ v1_relat_1(sK2)
% 3.26/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_462,c_32]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2658,plain,
% 3.26/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.26/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3189,plain,
% 3.26/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_2658,c_32,c_30,c_462,c_2951]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5636,plain,
% 3.26/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.26/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_5632,c_2991,c_3189]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5637,plain,
% 3.26/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.26/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 3.26/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.98      inference(demodulation,[status(thm)],[c_5636,c_2991]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_41,plain,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2952,plain,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.26/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_2951]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2663,plain,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_24,plain,
% 3.26/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_33,negated_conjecture,
% 3.26/0.98      ( l1_struct_0(sK1) ),
% 3.26/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_381,plain,
% 3.26/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_382,plain,
% 3.26/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_381]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_35,negated_conjecture,
% 3.26/0.98      ( l1_struct_0(sK0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_386,plain,
% 3.26/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_387,plain,
% 3.26/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_386]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2688,plain,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_2663,c_382,c_387]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_9,plain,
% 3.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2666,plain,
% 3.26/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.26/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3187,plain,
% 3.26/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_2688,c_2666]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_29,negated_conjecture,
% 3.26/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.26/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2685,plain,
% 3.26/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_29,c_382,c_387]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3466,plain,
% 3.26/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.26/0.98      inference(demodulation,[status(thm)],[c_3187,c_2685]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3675,plain,
% 3.26/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.26/0.98      inference(demodulation,[status(thm)],[c_3466,c_2688]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_8,plain,
% 3.26/0.98      ( v4_relat_1(X0,X1)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.26/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_20,plain,
% 3.26/0.98      ( ~ v1_partfun1(X0,X1)
% 3.26/0.98      | ~ v4_relat_1(X0,X1)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(X0) = X1 ),
% 3.26/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_393,plain,
% 3.26/0.98      ( ~ v1_partfun1(X0,X1)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(X0) = X1 ),
% 3.26/0.98      inference(resolution,[status(thm)],[c_8,c_20]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_397,plain,
% 3.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | ~ v1_partfun1(X0,X1)
% 3.26/0.98      | k1_relat_1(X0) = X1 ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_393,c_20,c_8,c_7]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_398,plain,
% 3.26/0.98      ( ~ v1_partfun1(X0,X1)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | k1_relat_1(X0) = X1 ),
% 3.26/0.98      inference(renaming,[status(thm)],[c_397]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2660,plain,
% 3.26/0.98      ( k1_relat_1(X0) = X1
% 3.26/0.98      | v1_partfun1(X0,X1) != iProver_top
% 3.26/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_4868,plain,
% 3.26/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.26/0.98      | v1_partfun1(sK2,k2_struct_0(sK0)) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_3675,c_2660]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_11,plain,
% 3.26/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.98      | v1_partfun1(X0,X1)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | v1_xboole_0(X2) ),
% 3.26/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_31,negated_conjecture,
% 3.26/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1290,plain,
% 3.26/0.98      ( v1_partfun1(X0,X1)
% 3.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | v1_xboole_0(X2)
% 3.26/0.98      | u1_struct_0(sK0) != X1
% 3.26/0.98      | u1_struct_0(sK1) != X2
% 3.26/0.98      | sK2 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1291,plain,
% 3.26/0.98      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 3.26/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.26/0.98      | ~ v1_funct_1(sK2)
% 3.26/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_1290]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1293,plain,
% 3.26/0.98      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 3.26/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_1291,c_32,c_30]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2652,plain,
% 3.26/0.98      ( v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top
% 3.26/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2691,plain,
% 3.26/0.98      ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
% 3.26/0.98      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_2652,c_382,c_387]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_25,plain,
% 3.26/0.99      ( v2_struct_0(X0)
% 3.26/0.99      | ~ l1_struct_0(X0)
% 3.26/0.99      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_34,negated_conjecture,
% 3.26/0.99      ( ~ v2_struct_0(sK1) ),
% 3.26/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_368,plain,
% 3.26/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_369,plain,
% 3.26/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_371,plain,
% 3.26/0.99      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_369,c_33]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2661,plain,
% 3.26/0.99      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2694,plain,
% 3.26/0.99      ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2691,c_2661]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4967,plain,
% 3.26/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_4868,c_2694]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_27,negated_conjecture,
% 3.26/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.26/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_26,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v2_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_437,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.26/0.99      | sK2 != X0 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_438,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_442,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_438,c_32]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_443,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_442]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1470,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | u1_struct_0(sK0) != X0
% 3.26/0.99      | u1_struct_0(sK1) != X1
% 3.26/0.99      | sK2 != sK2 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_443]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1471,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.26/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_1470]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1473,plain,
% 3.26/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_1471,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2740,plain,
% 3.26/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.26/0.99      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.26/0.99      inference(light_normalisation,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_1473,c_382,c_387,c_2685]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2741,plain,
% 3.26/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.26/0.99      inference(equality_resolution_simp,[status(thm)],[c_2740]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2819,plain,
% 3.26/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 3.26/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.26/0.99      inference(light_normalisation,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_27,c_382,c_387,c_2741]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3677,plain,
% 3.26/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.26/0.99      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_3466,c_2819]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4975,plain,
% 3.26/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.26/0.99      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_4967,c_3677]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2664,plain,
% 3.26/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top
% 3.26/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3574,plain,
% 3.26/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.26/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_2991,c_2664]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3587,plain,
% 3.26/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.26/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_3574,c_3189]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_39,plain,
% 3.26/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2944,plain,
% 3.26/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | ~ v1_relat_1(sK2) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2945,plain,
% 3.26/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top
% 3.26/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2944]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2947,plain,
% 3.26/0.99      ( ~ v1_funct_1(sK2)
% 3.26/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.26/0.99      | ~ v1_relat_1(sK2) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2948,plain,
% 3.26/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.26/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.26/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2947]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4366,plain,
% 3.26/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_3587,c_39,c_41,c_2945,c_2948,c_2952]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4374,plain,
% 3.26/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_4366,c_2666]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4376,plain,
% 3.26/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_4374,c_2991]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4984,plain,
% 3.26/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.26/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_4975,c_4376]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4985,plain,
% 3.26/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 3.26/0.99      inference(equality_resolution_simp,[status(thm)],[c_4984]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5867,plain,
% 3.26/0.99      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_5637,c_41,c_2952,c_4985]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_10,plain,
% 3.26/0.99      ( ~ v1_partfun1(X0,X1)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_xboole_0(X2)
% 3.26/0.99      | v1_xboole_0(X1) ),
% 3.26/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2665,plain,
% 3.26/0.99      ( v1_partfun1(X0,X1) != iProver_top
% 3.26/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.26/0.99      | v1_xboole_0(X2) != iProver_top
% 3.26/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4372,plain,
% 3.26/0.99      ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.26/0.99      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 3.26/0.99      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_4366,c_2665]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3676,plain,
% 3.26/0.99      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_3466,c_2661]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_19,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.26/0.99      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.26/0.99      | ~ v1_relat_1(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_413,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.26/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.26/0.99      | ~ v1_relat_1(X0)
% 3.26/0.99      | X0 != X1
% 3.26/0.99      | k1_relat_1(X0) != X2 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_414,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.26/0.99      | ~ v1_relat_1(X0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_424,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
% 3.26/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_414,c_7]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2659,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 3.26/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4168,plain,
% 3.26/0.99      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top
% 3.26/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_2664,c_2659]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4191,plain,
% 3.26/0.99      ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.26/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_3189,c_4168]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4695,plain,
% 3.26/0.99      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_4372,c_39,c_41,c_2945,c_2948,c_2952,c_3676,c_4191]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5878,plain,
% 3.26/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_5867,c_4695]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_0,plain,
% 3.26/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_113,plain,
% 3.26/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(contradiction,plain,
% 3.26/0.99      ( $false ),
% 3.26/0.99      inference(minisat,[status(thm)],[c_5878,c_113]) ).
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  ------                               Statistics
% 3.26/0.99  
% 3.26/0.99  ------ General
% 3.26/0.99  
% 3.26/0.99  abstr_ref_over_cycles:                  0
% 3.26/0.99  abstr_ref_under_cycles:                 0
% 3.26/0.99  gc_basic_clause_elim:                   0
% 3.26/0.99  forced_gc_time:                         0
% 3.26/0.99  parsing_time:                           0.01
% 3.26/0.99  unif_index_cands_time:                  0.
% 3.26/0.99  unif_index_add_time:                    0.
% 3.26/0.99  orderings_time:                         0.
% 3.26/0.99  out_proof_time:                         0.03
% 3.26/0.99  total_time:                             0.269
% 3.26/0.99  num_of_symbols:                         55
% 3.26/0.99  num_of_terms:                           4897
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing
% 3.26/0.99  
% 3.26/0.99  num_of_splits:                          0
% 3.26/0.99  num_of_split_atoms:                     0
% 3.26/0.99  num_of_reused_defs:                     0
% 3.26/0.99  num_eq_ax_congr_red:                    3
% 3.26/0.99  num_of_sem_filtered_clauses:            1
% 3.26/0.99  num_of_subtypes:                        0
% 3.26/0.99  monotx_restored_types:                  0
% 3.26/0.99  sat_num_of_epr_types:                   0
% 3.26/0.99  sat_num_of_non_cyclic_types:            0
% 3.26/0.99  sat_guarded_non_collapsed_types:        0
% 3.26/0.99  num_pure_diseq_elim:                    0
% 3.26/0.99  simp_replaced_by:                       0
% 3.26/0.99  res_preprocessed:                       174
% 3.26/0.99  prep_upred:                             0
% 3.26/0.99  prep_unflattend:                        129
% 3.26/0.99  smt_new_axioms:                         0
% 3.26/0.99  pred_elim_cands:                        5
% 3.26/0.99  pred_elim:                              5
% 3.26/0.99  pred_elim_cl:                           -1
% 3.26/0.99  pred_elim_cycles:                       9
% 3.26/0.99  merged_defs:                            0
% 3.26/0.99  merged_defs_ncl:                        0
% 3.26/0.99  bin_hyper_res:                          0
% 3.26/0.99  prep_cycles:                            4
% 3.26/0.99  pred_elim_time:                         0.05
% 3.26/0.99  splitting_time:                         0.
% 3.26/0.99  sem_filter_time:                        0.
% 3.26/0.99  monotx_time:                            0.
% 3.26/0.99  subtype_inf_time:                       0.
% 3.26/0.99  
% 3.26/0.99  ------ Problem properties
% 3.26/0.99  
% 3.26/0.99  clauses:                                35
% 3.26/0.99  conjectures:                            4
% 3.26/0.99  epr:                                    2
% 3.26/0.99  horn:                                   25
% 3.26/0.99  ground:                                 16
% 3.26/0.99  unary:                                  8
% 3.26/0.99  binary:                                 10
% 3.26/0.99  lits:                                   97
% 3.26/0.99  lits_eq:                                40
% 3.26/0.99  fd_pure:                                0
% 3.26/0.99  fd_pseudo:                              0
% 3.26/0.99  fd_cond:                                4
% 3.26/0.99  fd_pseudo_cond:                         1
% 3.26/0.99  ac_symbols:                             0
% 3.26/0.99  
% 3.26/0.99  ------ Propositional Solver
% 3.26/0.99  
% 3.26/0.99  prop_solver_calls:                      28
% 3.26/0.99  prop_fast_solver_calls:                 1551
% 3.26/0.99  smt_solver_calls:                       0
% 3.26/0.99  smt_fast_solver_calls:                  0
% 3.26/0.99  prop_num_of_clauses:                    1712
% 3.26/0.99  prop_preprocess_simplified:             6145
% 3.26/0.99  prop_fo_subsumed:                       51
% 3.26/0.99  prop_solver_time:                       0.
% 3.26/0.99  smt_solver_time:                        0.
% 3.26/0.99  smt_fast_solver_time:                   0.
% 3.26/0.99  prop_fast_solver_time:                  0.
% 3.26/0.99  prop_unsat_core_time:                   0.
% 3.26/0.99  
% 3.26/0.99  ------ QBF
% 3.26/0.99  
% 3.26/0.99  qbf_q_res:                              0
% 3.26/0.99  qbf_num_tautologies:                    0
% 3.26/0.99  qbf_prep_cycles:                        0
% 3.26/0.99  
% 3.26/0.99  ------ BMC1
% 3.26/0.99  
% 3.26/0.99  bmc1_current_bound:                     -1
% 3.26/0.99  bmc1_last_solved_bound:                 -1
% 3.26/0.99  bmc1_unsat_core_size:                   -1
% 3.26/0.99  bmc1_unsat_core_parents_size:           -1
% 3.26/0.99  bmc1_merge_next_fun:                    0
% 3.26/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation
% 3.26/0.99  
% 3.26/0.99  inst_num_of_clauses:                    564
% 3.26/0.99  inst_num_in_passive:                    74
% 3.26/0.99  inst_num_in_active:                     378
% 3.26/0.99  inst_num_in_unprocessed:                112
% 3.26/0.99  inst_num_of_loops:                      390
% 3.26/0.99  inst_num_of_learning_restarts:          0
% 3.26/0.99  inst_num_moves_active_passive:          9
% 3.26/0.99  inst_lit_activity:                      0
% 3.26/0.99  inst_lit_activity_moves:                0
% 3.26/0.99  inst_num_tautologies:                   0
% 3.26/0.99  inst_num_prop_implied:                  0
% 3.26/0.99  inst_num_existing_simplified:           0
% 3.26/0.99  inst_num_eq_res_simplified:             0
% 3.26/0.99  inst_num_child_elim:                    0
% 3.26/0.99  inst_num_of_dismatching_blockings:      66
% 3.26/0.99  inst_num_of_non_proper_insts:           485
% 3.26/0.99  inst_num_of_duplicates:                 0
% 3.26/0.99  inst_inst_num_from_inst_to_res:         0
% 3.26/0.99  inst_dismatching_checking_time:         0.
% 3.26/0.99  
% 3.26/0.99  ------ Resolution
% 3.26/0.99  
% 3.26/0.99  res_num_of_clauses:                     0
% 3.26/0.99  res_num_in_passive:                     0
% 3.26/0.99  res_num_in_active:                      0
% 3.26/0.99  res_num_of_loops:                       178
% 3.26/0.99  res_forward_subset_subsumed:            66
% 3.26/0.99  res_backward_subset_subsumed:           4
% 3.26/0.99  res_forward_subsumed:                   0
% 3.26/0.99  res_backward_subsumed:                  0
% 3.26/0.99  res_forward_subsumption_resolution:     6
% 3.26/0.99  res_backward_subsumption_resolution:    0
% 3.26/0.99  res_clause_to_clause_subsumption:       252
% 3.26/0.99  res_orphan_elimination:                 0
% 3.26/0.99  res_tautology_del:                      85
% 3.26/0.99  res_num_eq_res_simplified:              0
% 3.26/0.99  res_num_sel_changes:                    0
% 3.26/0.99  res_moves_from_active_to_pass:          0
% 3.26/0.99  
% 3.26/0.99  ------ Superposition
% 3.26/0.99  
% 3.26/0.99  sup_time_total:                         0.
% 3.26/0.99  sup_time_generating:                    0.
% 3.26/0.99  sup_time_sim_full:                      0.
% 3.26/0.99  sup_time_sim_immed:                     0.
% 3.26/0.99  
% 3.26/0.99  sup_num_of_clauses:                     54
% 3.26/0.99  sup_num_in_active:                      44
% 3.26/0.99  sup_num_in_passive:                     10
% 3.26/0.99  sup_num_of_loops:                       76
% 3.26/0.99  sup_fw_superposition:                   38
% 3.26/0.99  sup_bw_superposition:                   18
% 3.26/0.99  sup_immediate_simplified:               23
% 3.26/0.99  sup_given_eliminated:                   0
% 3.26/0.99  comparisons_done:                       0
% 3.26/0.99  comparisons_avoided:                    11
% 3.26/0.99  
% 3.26/0.99  ------ Simplifications
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  sim_fw_subset_subsumed:                 14
% 3.26/0.99  sim_bw_subset_subsumed:                 2
% 3.26/0.99  sim_fw_subsumed:                        1
% 3.26/0.99  sim_bw_subsumed:                        0
% 3.26/0.99  sim_fw_subsumption_res:                 2
% 3.26/0.99  sim_bw_subsumption_res:                 0
% 3.26/0.99  sim_tautology_del:                      2
% 3.26/0.99  sim_eq_tautology_del:                   3
% 3.26/0.99  sim_eq_res_simp:                        4
% 3.26/0.99  sim_fw_demodulated:                     4
% 3.26/0.99  sim_bw_demodulated:                     36
% 3.26/0.99  sim_light_normalised:                   17
% 3.26/0.99  sim_joinable_taut:                      0
% 3.26/0.99  sim_joinable_simp:                      0
% 3.26/0.99  sim_ac_normalised:                      0
% 3.26/0.99  sim_smt_subsumption:                    0
% 3.26/0.99  
%------------------------------------------------------------------------------
