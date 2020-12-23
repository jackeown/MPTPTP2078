%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:17 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 767 expanded)
%              Number of clauses        :   83 ( 221 expanded)
%              Number of leaves         :   15 ( 230 expanded)
%              Depth                    :   17
%              Number of atoms          :  430 (5585 expanded)
%              Number of equality atoms :  215 (1948 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_344,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_345,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_789,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_286,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_287,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_291,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_292,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_823,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_789,c_287,c_292])).

cnf(c_979,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_823])).

cnf(c_706,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_903,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_898,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_964,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_965,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1039,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1040,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_1320,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_979,c_903,c_965,c_1040])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_322,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_323,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_325,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_21])).

cnf(c_790,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1325,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_1320,c_790])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_413,plain,
    ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_414,plain,
    ( k3_relset_1(X0,X1,sK2) = k4_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_818,plain,
    ( k3_relset_1(X0,X1,sK2) = k4_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_414,c_287,c_292])).

cnf(c_974,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_818])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_395,plain,
    ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k2_relset_1(X1,X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_396,plain,
    ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k2_relset_1(X1,X0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_835,plain,
    ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k2_relset_1(X1,X0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_396,c_287,c_292])).

cnf(c_1067,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_835])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_801,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_18,c_287,c_292])).

cnf(c_1068,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1067,c_801])).

cnf(c_1261,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_974,c_1068])).

cnf(c_1396,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1325,c_1261])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_404,plain,
    ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k1_relset_1(X1,X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_405,plain,
    ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k1_relset_1(X1,X0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_830,plain,
    ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k1_relset_1(X1,X0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_405,c_287,c_292])).

cnf(c_1064,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_830])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_359,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_360,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_605,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK1) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_360])).

cnf(c_606,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_808,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_606,c_287,c_292])).

cnf(c_809,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_808,c_287])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_259,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_277,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_23])).

cnf(c_278,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_280,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_22])).

cnf(c_796,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_280,c_287])).

cnf(c_812,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_809,c_796])).

cnf(c_1326,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1064,c_812,c_974])).

cnf(c_1395,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1325,c_1326])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_298,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_299,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_21])).

cnf(c_304,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_487,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_304])).

cnf(c_597,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK1) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_487])).

cnf(c_598,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_814,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_598,c_287,c_292,c_801])).

cnf(c_815,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_814])).

cnf(c_847,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_16,c_287,c_292,c_815])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1396,c_1395,c_847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.81/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/0.99  
% 1.81/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/0.99  
% 1.81/0.99  ------  iProver source info
% 1.81/0.99  
% 1.81/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.81/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/0.99  git: non_committed_changes: false
% 1.81/0.99  git: last_make_outside_of_git: false
% 1.81/0.99  
% 1.81/0.99  ------ 
% 1.81/0.99  
% 1.81/0.99  ------ Input Options
% 1.81/0.99  
% 1.81/0.99  --out_options                           all
% 1.81/0.99  --tptp_safe_out                         true
% 1.81/0.99  --problem_path                          ""
% 1.81/0.99  --include_path                          ""
% 1.81/0.99  --clausifier                            res/vclausify_rel
% 1.81/0.99  --clausifier_options                    --mode clausify
% 1.81/0.99  --stdin                                 false
% 1.81/0.99  --stats_out                             all
% 1.81/0.99  
% 1.81/0.99  ------ General Options
% 1.81/0.99  
% 1.81/0.99  --fof                                   false
% 1.81/0.99  --time_out_real                         305.
% 1.81/0.99  --time_out_virtual                      -1.
% 1.81/0.99  --symbol_type_check                     false
% 1.81/0.99  --clausify_out                          false
% 1.81/0.99  --sig_cnt_out                           false
% 1.81/0.99  --trig_cnt_out                          false
% 1.81/0.99  --trig_cnt_out_tolerance                1.
% 1.81/0.99  --trig_cnt_out_sk_spl                   false
% 1.81/0.99  --abstr_cl_out                          false
% 1.81/0.99  
% 1.81/0.99  ------ Global Options
% 1.81/0.99  
% 1.81/0.99  --schedule                              default
% 1.81/0.99  --add_important_lit                     false
% 1.81/0.99  --prop_solver_per_cl                    1000
% 1.81/0.99  --min_unsat_core                        false
% 1.81/0.99  --soft_assumptions                      false
% 1.81/0.99  --soft_lemma_size                       3
% 1.81/0.99  --prop_impl_unit_size                   0
% 1.81/0.99  --prop_impl_unit                        []
% 1.81/0.99  --share_sel_clauses                     true
% 1.81/0.99  --reset_solvers                         false
% 1.81/0.99  --bc_imp_inh                            [conj_cone]
% 1.81/0.99  --conj_cone_tolerance                   3.
% 1.81/0.99  --extra_neg_conj                        none
% 1.81/0.99  --large_theory_mode                     true
% 1.81/0.99  --prolific_symb_bound                   200
% 1.81/0.99  --lt_threshold                          2000
% 1.81/0.99  --clause_weak_htbl                      true
% 1.81/0.99  --gc_record_bc_elim                     false
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing Options
% 1.81/0.99  
% 1.81/0.99  --preprocessing_flag                    true
% 1.81/0.99  --time_out_prep_mult                    0.1
% 1.81/0.99  --splitting_mode                        input
% 1.81/0.99  --splitting_grd                         true
% 1.81/0.99  --splitting_cvd                         false
% 1.81/0.99  --splitting_cvd_svl                     false
% 1.81/0.99  --splitting_nvd                         32
% 1.81/0.99  --sub_typing                            true
% 1.81/0.99  --prep_gs_sim                           true
% 1.81/0.99  --prep_unflatten                        true
% 1.81/0.99  --prep_res_sim                          true
% 1.81/0.99  --prep_upred                            true
% 1.81/0.99  --prep_sem_filter                       exhaustive
% 1.81/0.99  --prep_sem_filter_out                   false
% 1.81/0.99  --pred_elim                             true
% 1.81/0.99  --res_sim_input                         true
% 1.81/0.99  --eq_ax_congr_red                       true
% 1.81/0.99  --pure_diseq_elim                       true
% 1.81/0.99  --brand_transform                       false
% 1.81/0.99  --non_eq_to_eq                          false
% 1.81/0.99  --prep_def_merge                        true
% 1.81/0.99  --prep_def_merge_prop_impl              false
% 1.81/0.99  --prep_def_merge_mbd                    true
% 1.81/0.99  --prep_def_merge_tr_red                 false
% 1.81/0.99  --prep_def_merge_tr_cl                  false
% 1.81/0.99  --smt_preprocessing                     true
% 1.81/0.99  --smt_ac_axioms                         fast
% 1.81/0.99  --preprocessed_out                      false
% 1.81/0.99  --preprocessed_stats                    false
% 1.81/0.99  
% 1.81/0.99  ------ Abstraction refinement Options
% 1.81/0.99  
% 1.81/0.99  --abstr_ref                             []
% 1.81/0.99  --abstr_ref_prep                        false
% 1.81/0.99  --abstr_ref_until_sat                   false
% 1.81/0.99  --abstr_ref_sig_restrict                funpre
% 1.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.99  --abstr_ref_under                       []
% 1.81/0.99  
% 1.81/0.99  ------ SAT Options
% 1.81/0.99  
% 1.81/0.99  --sat_mode                              false
% 1.81/0.99  --sat_fm_restart_options                ""
% 1.81/0.99  --sat_gr_def                            false
% 1.81/0.99  --sat_epr_types                         true
% 1.81/0.99  --sat_non_cyclic_types                  false
% 1.81/0.99  --sat_finite_models                     false
% 1.81/0.99  --sat_fm_lemmas                         false
% 1.81/0.99  --sat_fm_prep                           false
% 1.81/0.99  --sat_fm_uc_incr                        true
% 1.81/0.99  --sat_out_model                         small
% 1.81/0.99  --sat_out_clauses                       false
% 1.81/0.99  
% 1.81/0.99  ------ QBF Options
% 1.81/0.99  
% 1.81/0.99  --qbf_mode                              false
% 1.81/0.99  --qbf_elim_univ                         false
% 1.81/0.99  --qbf_dom_inst                          none
% 1.81/0.99  --qbf_dom_pre_inst                      false
% 1.81/0.99  --qbf_sk_in                             false
% 1.81/0.99  --qbf_pred_elim                         true
% 1.81/0.99  --qbf_split                             512
% 1.81/0.99  
% 1.81/0.99  ------ BMC1 Options
% 1.81/0.99  
% 1.81/0.99  --bmc1_incremental                      false
% 1.81/0.99  --bmc1_axioms                           reachable_all
% 1.81/0.99  --bmc1_min_bound                        0
% 1.81/0.99  --bmc1_max_bound                        -1
% 1.81/0.99  --bmc1_max_bound_default                -1
% 1.81/0.99  --bmc1_symbol_reachability              true
% 1.81/0.99  --bmc1_property_lemmas                  false
% 1.81/0.99  --bmc1_k_induction                      false
% 1.81/0.99  --bmc1_non_equiv_states                 false
% 1.81/0.99  --bmc1_deadlock                         false
% 1.81/0.99  --bmc1_ucm                              false
% 1.81/0.99  --bmc1_add_unsat_core                   none
% 1.81/0.99  --bmc1_unsat_core_children              false
% 1.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.99  --bmc1_out_stat                         full
% 1.81/0.99  --bmc1_ground_init                      false
% 1.81/0.99  --bmc1_pre_inst_next_state              false
% 1.81/0.99  --bmc1_pre_inst_state                   false
% 1.81/0.99  --bmc1_pre_inst_reach_state             false
% 1.81/0.99  --bmc1_out_unsat_core                   false
% 1.81/0.99  --bmc1_aig_witness_out                  false
% 1.81/0.99  --bmc1_verbose                          false
% 1.81/0.99  --bmc1_dump_clauses_tptp                false
% 1.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.99  --bmc1_dump_file                        -
% 1.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.99  --bmc1_ucm_extend_mode                  1
% 1.81/0.99  --bmc1_ucm_init_mode                    2
% 1.81/0.99  --bmc1_ucm_cone_mode                    none
% 1.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.99  --bmc1_ucm_relax_model                  4
% 1.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.99  --bmc1_ucm_layered_model                none
% 1.81/0.99  --bmc1_ucm_max_lemma_size               10
% 1.81/0.99  
% 1.81/0.99  ------ AIG Options
% 1.81/0.99  
% 1.81/0.99  --aig_mode                              false
% 1.81/0.99  
% 1.81/0.99  ------ Instantiation Options
% 1.81/0.99  
% 1.81/0.99  --instantiation_flag                    true
% 1.81/0.99  --inst_sos_flag                         false
% 1.81/0.99  --inst_sos_phase                        true
% 1.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.99  --inst_lit_sel_side                     num_symb
% 1.81/0.99  --inst_solver_per_active                1400
% 1.81/0.99  --inst_solver_calls_frac                1.
% 1.81/0.99  --inst_passive_queue_type               priority_queues
% 1.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.99  --inst_passive_queues_freq              [25;2]
% 1.81/0.99  --inst_dismatching                      true
% 1.81/0.99  --inst_eager_unprocessed_to_passive     true
% 1.81/0.99  --inst_prop_sim_given                   true
% 1.81/0.99  --inst_prop_sim_new                     false
% 1.81/0.99  --inst_subs_new                         false
% 1.81/0.99  --inst_eq_res_simp                      false
% 1.81/0.99  --inst_subs_given                       false
% 1.81/0.99  --inst_orphan_elimination               true
% 1.81/0.99  --inst_learning_loop_flag               true
% 1.81/0.99  --inst_learning_start                   3000
% 1.81/0.99  --inst_learning_factor                  2
% 1.81/0.99  --inst_start_prop_sim_after_learn       3
% 1.81/0.99  --inst_sel_renew                        solver
% 1.81/0.99  --inst_lit_activity_flag                true
% 1.81/0.99  --inst_restr_to_given                   false
% 1.81/0.99  --inst_activity_threshold               500
% 1.81/0.99  --inst_out_proof                        true
% 1.81/0.99  
% 1.81/0.99  ------ Resolution Options
% 1.81/0.99  
% 1.81/0.99  --resolution_flag                       true
% 1.81/0.99  --res_lit_sel                           adaptive
% 1.81/0.99  --res_lit_sel_side                      none
% 1.81/0.99  --res_ordering                          kbo
% 1.81/0.99  --res_to_prop_solver                    active
% 1.81/0.99  --res_prop_simpl_new                    false
% 1.81/0.99  --res_prop_simpl_given                  true
% 1.81/0.99  --res_passive_queue_type                priority_queues
% 1.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.99  --res_passive_queues_freq               [15;5]
% 1.81/0.99  --res_forward_subs                      full
% 1.81/0.99  --res_backward_subs                     full
% 1.81/0.99  --res_forward_subs_resolution           true
% 1.81/0.99  --res_backward_subs_resolution          true
% 1.81/0.99  --res_orphan_elimination                true
% 1.81/0.99  --res_time_limit                        2.
% 1.81/0.99  --res_out_proof                         true
% 1.81/0.99  
% 1.81/0.99  ------ Superposition Options
% 1.81/0.99  
% 1.81/0.99  --superposition_flag                    true
% 1.81/0.99  --sup_passive_queue_type                priority_queues
% 1.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.99  --demod_completeness_check              fast
% 1.81/0.99  --demod_use_ground                      true
% 1.81/0.99  --sup_to_prop_solver                    passive
% 1.81/0.99  --sup_prop_simpl_new                    true
% 1.81/0.99  --sup_prop_simpl_given                  true
% 1.81/0.99  --sup_fun_splitting                     false
% 1.81/0.99  --sup_smt_interval                      50000
% 1.81/0.99  
% 1.81/0.99  ------ Superposition Simplification Setup
% 1.81/0.99  
% 1.81/0.99  --sup_indices_passive                   []
% 1.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_full_bw                           [BwDemod]
% 1.81/0.99  --sup_immed_triv                        [TrivRules]
% 1.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_immed_bw_main                     []
% 1.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.99  
% 1.81/0.99  ------ Combination Options
% 1.81/0.99  
% 1.81/0.99  --comb_res_mult                         3
% 1.81/0.99  --comb_sup_mult                         2
% 1.81/0.99  --comb_inst_mult                        10
% 1.81/0.99  
% 1.81/0.99  ------ Debug Options
% 1.81/0.99  
% 1.81/0.99  --dbg_backtrace                         false
% 1.81/0.99  --dbg_dump_prop_clauses                 false
% 1.81/0.99  --dbg_dump_prop_clauses_file            -
% 1.81/0.99  --dbg_out_stat                          false
% 1.81/0.99  ------ Parsing...
% 1.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/0.99  ------ Proving...
% 1.81/0.99  ------ Problem Properties 
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  clauses                                 17
% 1.81/0.99  conjectures                             2
% 1.81/0.99  EPR                                     0
% 1.81/0.99  Horn                                    14
% 1.81/0.99  unary                                   5
% 1.81/0.99  binary                                  7
% 1.81/0.99  lits                                    39
% 1.81/0.99  lits eq                                 35
% 1.81/0.99  fd_pure                                 0
% 1.81/0.99  fd_pseudo                               0
% 1.81/0.99  fd_cond                                 2
% 1.81/0.99  fd_pseudo_cond                          0
% 1.81/0.99  AC symbols                              0
% 1.81/0.99  
% 1.81/0.99  ------ Schedule dynamic 5 is on 
% 1.81/0.99  
% 1.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  ------ 
% 1.81/0.99  Current options:
% 1.81/0.99  ------ 
% 1.81/0.99  
% 1.81/0.99  ------ Input Options
% 1.81/0.99  
% 1.81/0.99  --out_options                           all
% 1.81/0.99  --tptp_safe_out                         true
% 1.81/0.99  --problem_path                          ""
% 1.81/0.99  --include_path                          ""
% 1.81/0.99  --clausifier                            res/vclausify_rel
% 1.81/0.99  --clausifier_options                    --mode clausify
% 1.81/0.99  --stdin                                 false
% 1.81/0.99  --stats_out                             all
% 1.81/0.99  
% 1.81/0.99  ------ General Options
% 1.81/0.99  
% 1.81/0.99  --fof                                   false
% 1.81/0.99  --time_out_real                         305.
% 1.81/0.99  --time_out_virtual                      -1.
% 1.81/0.99  --symbol_type_check                     false
% 1.81/0.99  --clausify_out                          false
% 1.81/0.99  --sig_cnt_out                           false
% 1.81/0.99  --trig_cnt_out                          false
% 1.81/0.99  --trig_cnt_out_tolerance                1.
% 1.81/0.99  --trig_cnt_out_sk_spl                   false
% 1.81/0.99  --abstr_cl_out                          false
% 1.81/0.99  
% 1.81/0.99  ------ Global Options
% 1.81/0.99  
% 1.81/0.99  --schedule                              default
% 1.81/0.99  --add_important_lit                     false
% 1.81/0.99  --prop_solver_per_cl                    1000
% 1.81/0.99  --min_unsat_core                        false
% 1.81/0.99  --soft_assumptions                      false
% 1.81/0.99  --soft_lemma_size                       3
% 1.81/0.99  --prop_impl_unit_size                   0
% 1.81/0.99  --prop_impl_unit                        []
% 1.81/0.99  --share_sel_clauses                     true
% 1.81/0.99  --reset_solvers                         false
% 1.81/0.99  --bc_imp_inh                            [conj_cone]
% 1.81/0.99  --conj_cone_tolerance                   3.
% 1.81/0.99  --extra_neg_conj                        none
% 1.81/0.99  --large_theory_mode                     true
% 1.81/0.99  --prolific_symb_bound                   200
% 1.81/0.99  --lt_threshold                          2000
% 1.81/0.99  --clause_weak_htbl                      true
% 1.81/0.99  --gc_record_bc_elim                     false
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing Options
% 1.81/0.99  
% 1.81/0.99  --preprocessing_flag                    true
% 1.81/0.99  --time_out_prep_mult                    0.1
% 1.81/0.99  --splitting_mode                        input
% 1.81/0.99  --splitting_grd                         true
% 1.81/0.99  --splitting_cvd                         false
% 1.81/0.99  --splitting_cvd_svl                     false
% 1.81/0.99  --splitting_nvd                         32
% 1.81/0.99  --sub_typing                            true
% 1.81/0.99  --prep_gs_sim                           true
% 1.81/0.99  --prep_unflatten                        true
% 1.81/0.99  --prep_res_sim                          true
% 1.81/0.99  --prep_upred                            true
% 1.81/0.99  --prep_sem_filter                       exhaustive
% 1.81/0.99  --prep_sem_filter_out                   false
% 1.81/0.99  --pred_elim                             true
% 1.81/0.99  --res_sim_input                         true
% 1.81/0.99  --eq_ax_congr_red                       true
% 1.81/0.99  --pure_diseq_elim                       true
% 1.81/0.99  --brand_transform                       false
% 1.81/0.99  --non_eq_to_eq                          false
% 1.81/0.99  --prep_def_merge                        true
% 1.81/0.99  --prep_def_merge_prop_impl              false
% 1.81/0.99  --prep_def_merge_mbd                    true
% 1.81/0.99  --prep_def_merge_tr_red                 false
% 1.81/0.99  --prep_def_merge_tr_cl                  false
% 1.81/0.99  --smt_preprocessing                     true
% 1.81/0.99  --smt_ac_axioms                         fast
% 1.81/0.99  --preprocessed_out                      false
% 1.81/0.99  --preprocessed_stats                    false
% 1.81/0.99  
% 1.81/0.99  ------ Abstraction refinement Options
% 1.81/0.99  
% 1.81/0.99  --abstr_ref                             []
% 1.81/0.99  --abstr_ref_prep                        false
% 1.81/0.99  --abstr_ref_until_sat                   false
% 1.81/0.99  --abstr_ref_sig_restrict                funpre
% 1.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.99  --abstr_ref_under                       []
% 1.81/0.99  
% 1.81/0.99  ------ SAT Options
% 1.81/0.99  
% 1.81/0.99  --sat_mode                              false
% 1.81/0.99  --sat_fm_restart_options                ""
% 1.81/0.99  --sat_gr_def                            false
% 1.81/0.99  --sat_epr_types                         true
% 1.81/0.99  --sat_non_cyclic_types                  false
% 1.81/0.99  --sat_finite_models                     false
% 1.81/0.99  --sat_fm_lemmas                         false
% 1.81/0.99  --sat_fm_prep                           false
% 1.81/0.99  --sat_fm_uc_incr                        true
% 1.81/0.99  --sat_out_model                         small
% 1.81/0.99  --sat_out_clauses                       false
% 1.81/0.99  
% 1.81/0.99  ------ QBF Options
% 1.81/0.99  
% 1.81/0.99  --qbf_mode                              false
% 1.81/0.99  --qbf_elim_univ                         false
% 1.81/0.99  --qbf_dom_inst                          none
% 1.81/0.99  --qbf_dom_pre_inst                      false
% 1.81/0.99  --qbf_sk_in                             false
% 1.81/0.99  --qbf_pred_elim                         true
% 1.81/0.99  --qbf_split                             512
% 1.81/0.99  
% 1.81/0.99  ------ BMC1 Options
% 1.81/0.99  
% 1.81/0.99  --bmc1_incremental                      false
% 1.81/0.99  --bmc1_axioms                           reachable_all
% 1.81/0.99  --bmc1_min_bound                        0
% 1.81/0.99  --bmc1_max_bound                        -1
% 1.81/0.99  --bmc1_max_bound_default                -1
% 1.81/0.99  --bmc1_symbol_reachability              true
% 1.81/0.99  --bmc1_property_lemmas                  false
% 1.81/0.99  --bmc1_k_induction                      false
% 1.81/0.99  --bmc1_non_equiv_states                 false
% 1.81/0.99  --bmc1_deadlock                         false
% 1.81/0.99  --bmc1_ucm                              false
% 1.81/0.99  --bmc1_add_unsat_core                   none
% 1.81/0.99  --bmc1_unsat_core_children              false
% 1.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.99  --bmc1_out_stat                         full
% 1.81/0.99  --bmc1_ground_init                      false
% 1.81/0.99  --bmc1_pre_inst_next_state              false
% 1.81/0.99  --bmc1_pre_inst_state                   false
% 1.81/0.99  --bmc1_pre_inst_reach_state             false
% 1.81/0.99  --bmc1_out_unsat_core                   false
% 1.81/0.99  --bmc1_aig_witness_out                  false
% 1.81/0.99  --bmc1_verbose                          false
% 1.81/0.99  --bmc1_dump_clauses_tptp                false
% 1.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.99  --bmc1_dump_file                        -
% 1.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.99  --bmc1_ucm_extend_mode                  1
% 1.81/0.99  --bmc1_ucm_init_mode                    2
% 1.81/0.99  --bmc1_ucm_cone_mode                    none
% 1.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.99  --bmc1_ucm_relax_model                  4
% 1.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.99  --bmc1_ucm_layered_model                none
% 1.81/0.99  --bmc1_ucm_max_lemma_size               10
% 1.81/0.99  
% 1.81/0.99  ------ AIG Options
% 1.81/0.99  
% 1.81/0.99  --aig_mode                              false
% 1.81/0.99  
% 1.81/0.99  ------ Instantiation Options
% 1.81/0.99  
% 1.81/0.99  --instantiation_flag                    true
% 1.81/0.99  --inst_sos_flag                         false
% 1.81/0.99  --inst_sos_phase                        true
% 1.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.99  --inst_lit_sel_side                     none
% 1.81/0.99  --inst_solver_per_active                1400
% 1.81/0.99  --inst_solver_calls_frac                1.
% 1.81/0.99  --inst_passive_queue_type               priority_queues
% 1.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.99  --inst_passive_queues_freq              [25;2]
% 1.81/0.99  --inst_dismatching                      true
% 1.81/0.99  --inst_eager_unprocessed_to_passive     true
% 1.81/0.99  --inst_prop_sim_given                   true
% 1.81/0.99  --inst_prop_sim_new                     false
% 1.81/0.99  --inst_subs_new                         false
% 1.81/0.99  --inst_eq_res_simp                      false
% 1.81/0.99  --inst_subs_given                       false
% 1.81/0.99  --inst_orphan_elimination               true
% 1.81/0.99  --inst_learning_loop_flag               true
% 1.81/0.99  --inst_learning_start                   3000
% 1.81/0.99  --inst_learning_factor                  2
% 1.81/0.99  --inst_start_prop_sim_after_learn       3
% 1.81/0.99  --inst_sel_renew                        solver
% 1.81/0.99  --inst_lit_activity_flag                true
% 1.81/0.99  --inst_restr_to_given                   false
% 1.81/0.99  --inst_activity_threshold               500
% 1.81/0.99  --inst_out_proof                        true
% 1.81/0.99  
% 1.81/0.99  ------ Resolution Options
% 1.81/0.99  
% 1.81/0.99  --resolution_flag                       false
% 1.81/0.99  --res_lit_sel                           adaptive
% 1.81/0.99  --res_lit_sel_side                      none
% 1.81/0.99  --res_ordering                          kbo
% 1.81/0.99  --res_to_prop_solver                    active
% 1.81/0.99  --res_prop_simpl_new                    false
% 1.81/0.99  --res_prop_simpl_given                  true
% 1.81/0.99  --res_passive_queue_type                priority_queues
% 1.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.99  --res_passive_queues_freq               [15;5]
% 1.81/0.99  --res_forward_subs                      full
% 1.81/0.99  --res_backward_subs                     full
% 1.81/0.99  --res_forward_subs_resolution           true
% 1.81/0.99  --res_backward_subs_resolution          true
% 1.81/0.99  --res_orphan_elimination                true
% 1.81/0.99  --res_time_limit                        2.
% 1.81/0.99  --res_out_proof                         true
% 1.81/0.99  
% 1.81/0.99  ------ Superposition Options
% 1.81/0.99  
% 1.81/0.99  --superposition_flag                    true
% 1.81/0.99  --sup_passive_queue_type                priority_queues
% 1.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.99  --demod_completeness_check              fast
% 1.81/0.99  --demod_use_ground                      true
% 1.81/0.99  --sup_to_prop_solver                    passive
% 1.81/0.99  --sup_prop_simpl_new                    true
% 1.81/0.99  --sup_prop_simpl_given                  true
% 1.81/0.99  --sup_fun_splitting                     false
% 1.81/0.99  --sup_smt_interval                      50000
% 1.81/0.99  
% 1.81/0.99  ------ Superposition Simplification Setup
% 1.81/0.99  
% 1.81/0.99  --sup_indices_passive                   []
% 1.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_full_bw                           [BwDemod]
% 1.81/0.99  --sup_immed_triv                        [TrivRules]
% 1.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_immed_bw_main                     []
% 1.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.99  
% 1.81/0.99  ------ Combination Options
% 1.81/0.99  
% 1.81/0.99  --comb_res_mult                         3
% 1.81/0.99  --comb_sup_mult                         2
% 1.81/0.99  --comb_inst_mult                        10
% 1.81/0.99  
% 1.81/0.99  ------ Debug Options
% 1.81/0.99  
% 1.81/0.99  --dbg_backtrace                         false
% 1.81/0.99  --dbg_dump_prop_clauses                 false
% 1.81/0.99  --dbg_dump_prop_clauses_file            -
% 1.81/0.99  --dbg_out_stat                          false
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  ------ Proving...
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  % SZS status Theorem for theBenchmark.p
% 1.81/0.99  
% 1.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/0.99  
% 1.81/0.99  fof(f2,axiom,(
% 1.81/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f13,plain,(
% 1.81/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/0.99    inference(ennf_transformation,[],[f2])).
% 1.81/0.99  
% 1.81/0.99  fof(f33,plain,(
% 1.81/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/0.99    inference(cnf_transformation,[],[f13])).
% 1.81/0.99  
% 1.81/0.99  fof(f11,conjecture,(
% 1.81/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f12,negated_conjecture,(
% 1.81/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.81/0.99    inference(negated_conjecture,[],[f11])).
% 1.81/0.99  
% 1.81/0.99  fof(f25,plain,(
% 1.81/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.81/0.99    inference(ennf_transformation,[],[f12])).
% 1.81/0.99  
% 1.81/0.99  fof(f26,plain,(
% 1.81/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.81/0.99    inference(flattening,[],[f25])).
% 1.81/0.99  
% 1.81/0.99  fof(f30,plain,(
% 1.81/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.81/0.99    introduced(choice_axiom,[])).
% 1.81/0.99  
% 1.81/0.99  fof(f29,plain,(
% 1.81/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 1.81/0.99    introduced(choice_axiom,[])).
% 1.81/0.99  
% 1.81/0.99  fof(f28,plain,(
% 1.81/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.81/0.99    introduced(choice_axiom,[])).
% 1.81/0.99  
% 1.81/0.99  fof(f31,plain,(
% 1.81/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).
% 1.81/0.99  
% 1.81/0.99  fof(f53,plain,(
% 1.81/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f8,axiom,(
% 1.81/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f20,plain,(
% 1.81/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.81/0.99    inference(ennf_transformation,[],[f8])).
% 1.81/0.99  
% 1.81/0.99  fof(f45,plain,(
% 1.81/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.81/0.99    inference(cnf_transformation,[],[f20])).
% 1.81/0.99  
% 1.81/0.99  fof(f50,plain,(
% 1.81/0.99    l1_struct_0(sK1)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f48,plain,(
% 1.81/0.99    l1_struct_0(sK0)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f3,axiom,(
% 1.81/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f34,plain,(
% 1.81/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/0.99    inference(cnf_transformation,[],[f3])).
% 1.81/0.99  
% 1.81/0.99  fof(f4,axiom,(
% 1.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f14,plain,(
% 1.81/0.99    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.99    inference(ennf_transformation,[],[f4])).
% 1.81/0.99  
% 1.81/0.99  fof(f15,plain,(
% 1.81/0.99    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.99    inference(flattening,[],[f14])).
% 1.81/0.99  
% 1.81/0.99  fof(f35,plain,(
% 1.81/0.99    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.99    inference(cnf_transformation,[],[f15])).
% 1.81/0.99  
% 1.81/0.99  fof(f55,plain,(
% 1.81/0.99    v2_funct_1(sK2)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f51,plain,(
% 1.81/0.99    v1_funct_1(sK2)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f5,axiom,(
% 1.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f16,plain,(
% 1.81/0.99    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.99    inference(ennf_transformation,[],[f5])).
% 1.81/0.99  
% 1.81/0.99  fof(f36,plain,(
% 1.81/0.99    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.99    inference(cnf_transformation,[],[f16])).
% 1.81/0.99  
% 1.81/0.99  fof(f6,axiom,(
% 1.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f17,plain,(
% 1.81/0.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.99    inference(ennf_transformation,[],[f6])).
% 1.81/0.99  
% 1.81/0.99  fof(f37,plain,(
% 1.81/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.99    inference(cnf_transformation,[],[f17])).
% 1.81/0.99  
% 1.81/0.99  fof(f54,plain,(
% 1.81/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f38,plain,(
% 1.81/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.99    inference(cnf_transformation,[],[f17])).
% 1.81/0.99  
% 1.81/0.99  fof(f52,plain,(
% 1.81/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f7,axiom,(
% 1.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f18,plain,(
% 1.81/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.99    inference(ennf_transformation,[],[f7])).
% 1.81/0.99  
% 1.81/0.99  fof(f19,plain,(
% 1.81/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.99    inference(flattening,[],[f18])).
% 1.81/0.99  
% 1.81/0.99  fof(f27,plain,(
% 1.81/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.99    inference(nnf_transformation,[],[f19])).
% 1.81/0.99  
% 1.81/0.99  fof(f39,plain,(
% 1.81/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.99    inference(cnf_transformation,[],[f27])).
% 1.81/0.99  
% 1.81/0.99  fof(f1,axiom,(
% 1.81/0.99    v1_xboole_0(k1_xboole_0)),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f32,plain,(
% 1.81/0.99    v1_xboole_0(k1_xboole_0)),
% 1.81/0.99    inference(cnf_transformation,[],[f1])).
% 1.81/0.99  
% 1.81/0.99  fof(f9,axiom,(
% 1.81/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f21,plain,(
% 1.81/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.81/0.99    inference(ennf_transformation,[],[f9])).
% 1.81/0.99  
% 1.81/0.99  fof(f22,plain,(
% 1.81/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.81/0.99    inference(flattening,[],[f21])).
% 1.81/0.99  
% 1.81/0.99  fof(f46,plain,(
% 1.81/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.81/0.99    inference(cnf_transformation,[],[f22])).
% 1.81/0.99  
% 1.81/0.99  fof(f49,plain,(
% 1.81/0.99    ~v2_struct_0(sK1)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f56,plain,(
% 1.81/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 1.81/0.99    inference(cnf_transformation,[],[f31])).
% 1.81/0.99  
% 1.81/0.99  fof(f10,axiom,(
% 1.81/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.99  
% 1.81/0.99  fof(f23,plain,(
% 1.81/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/0.99    inference(ennf_transformation,[],[f10])).
% 1.81/0.99  
% 1.81/0.99  fof(f24,plain,(
% 1.81/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/0.99    inference(flattening,[],[f23])).
% 1.81/0.99  
% 1.81/0.99  fof(f47,plain,(
% 1.81/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/0.99    inference(cnf_transformation,[],[f24])).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1,plain,
% 1.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.81/0.99      | ~ v1_relat_1(X1)
% 1.81/0.99      | v1_relat_1(X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_19,negated_conjecture,
% 1.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.81/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_344,plain,
% 1.81/0.99      ( ~ v1_relat_1(X0)
% 1.81/0.99      | v1_relat_1(X1)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 1.81/0.99      | sK2 != X1 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_345,plain,
% 1.81/0.99      ( ~ v1_relat_1(X0)
% 1.81/0.99      | v1_relat_1(sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_789,plain,
% 1.81/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 1.81/0.99      | v1_relat_1(X0) != iProver_top
% 1.81/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.81/0.99      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_13,plain,
% 1.81/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_22,negated_conjecture,
% 1.81/0.99      ( l1_struct_0(sK1) ),
% 1.81/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_286,plain,
% 1.81/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_287,plain,
% 1.81/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_24,negated_conjecture,
% 1.81/0.99      ( l1_struct_0(sK0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_291,plain,
% 1.81/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_292,plain,
% 1.81/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_823,plain,
% 1.81/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
% 1.81/0.99      | v1_relat_1(X0) != iProver_top
% 1.81/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_789,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_979,plain,
% 1.81/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 1.81/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.81/0.99      inference(equality_resolution,[status(thm)],[c_823]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_706,plain,( X0 = X0 ),theory(equality) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_903,plain,
% 1.81/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.81/0.99      inference(instantiation,[status(thm)],[c_706]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_898,plain,
% 1.81/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | v1_relat_1(sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/0.99      inference(instantiation,[status(thm)],[c_345]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_964,plain,
% 1.81/0.99      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.81/0.99      | v1_relat_1(sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.81/0.99      inference(instantiation,[status(thm)],[c_898]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_965,plain,
% 1.81/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.81/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.81/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.81/0.99      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_2,plain,
% 1.81/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1039,plain,
% 1.81/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.81/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1040,plain,
% 1.81/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1320,plain,
% 1.81/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 1.81/0.99      inference(global_propositional_subsumption,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_979,c_903,c_965,c_1040]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_3,plain,
% 1.81/0.99      ( ~ v1_funct_1(X0)
% 1.81/0.99      | ~ v2_funct_1(X0)
% 1.81/0.99      | ~ v1_relat_1(X0)
% 1.81/0.99      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_17,negated_conjecture,
% 1.81/0.99      ( v2_funct_1(sK2) ),
% 1.81/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_322,plain,
% 1.81/0.99      ( ~ v1_funct_1(X0)
% 1.81/0.99      | ~ v1_relat_1(X0)
% 1.81/0.99      | k4_relat_1(X0) = k2_funct_1(X0)
% 1.81/0.99      | sK2 != X0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_323,plain,
% 1.81/0.99      ( ~ v1_funct_1(sK2)
% 1.81/0.99      | ~ v1_relat_1(sK2)
% 1.81/0.99      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_21,negated_conjecture,
% 1.81/0.99      ( v1_funct_1(sK2) ),
% 1.81/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_325,plain,
% 1.81/0.99      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 1.81/0.99      inference(global_propositional_subsumption,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_323,c_21]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_790,plain,
% 1.81/0.99      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 1.81/0.99      | v1_relat_1(sK2) != iProver_top ),
% 1.81/0.99      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1325,plain,
% 1.81/0.99      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 1.81/0.99      inference(superposition,[status(thm)],[c_1320,c_790]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_4,plain,
% 1.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_413,plain,
% 1.81/0.99      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | sK2 != X2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_414,plain,
% 1.81/0.99      ( k3_relset_1(X0,X1,sK2) = k4_relat_1(sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_818,plain,
% 1.81/0.99      ( k3_relset_1(X0,X1,sK2) = k4_relat_1(sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_414,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_974,plain,
% 1.81/0.99      ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 1.81/0.99      inference(equality_resolution,[status(thm)],[c_818]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_6,plain,
% 1.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_395,plain,
% 1.81/0.99      ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k2_relset_1(X1,X0,X2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 1.81/0.99      | sK2 != X2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_396,plain,
% 1.81/0.99      ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k2_relset_1(X1,X0,sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_835,plain,
% 1.81/0.99      ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k2_relset_1(X1,X0,sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_396,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1067,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 1.81/0.99      inference(equality_resolution,[status(thm)],[c_835]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_18,negated_conjecture,
% 1.81/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_801,plain,
% 1.81/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_18,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1068,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_1067,c_801]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1261,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(demodulation,[status(thm)],[c_974,c_1068]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1396,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1) ),
% 1.81/0.99      inference(demodulation,[status(thm)],[c_1325,c_1261]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_5,plain,
% 1.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_404,plain,
% 1.81/0.99      ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k1_relset_1(X1,X0,X2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 1.81/0.99      | sK2 != X2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_405,plain,
% 1.81/0.99      ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k1_relset_1(X1,X0,sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_830,plain,
% 1.81/0.99      ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,sK2)) = k1_relset_1(X1,X0,sK2)
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_405,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1064,plain,
% 1.81/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 1.81/0.99      inference(equality_resolution,[status(thm)],[c_830]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_20,negated_conjecture,
% 1.81/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.81/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_12,plain,
% 1.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.81/0.99      | k1_xboole_0 = X2 ),
% 1.81/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_359,plain,
% 1.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.81/0.99      | sK2 != X0
% 1.81/0.99      | k1_xboole_0 = X2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_360,plain,
% 1.81/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 1.81/0.99      | k1_relset_1(X0,X1,sK2) = X0
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | k1_xboole_0 = X1 ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_605,plain,
% 1.81/0.99      ( k1_relset_1(X0,X1,sK2) = X0
% 1.81/0.99      | u1_struct_0(sK0) != X0
% 1.81/0.99      | u1_struct_0(sK1) != X1
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | sK2 != sK2
% 1.81/0.99      | k1_xboole_0 = X1 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_360]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_606,plain,
% 1.81/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.81/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_808,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 1.81/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_606,c_287,c_292]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_809,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 1.81/0.99      | k2_struct_0(sK1) = k1_xboole_0 ),
% 1.81/0.99      inference(demodulation,[status(thm)],[c_808,c_287]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_0,plain,
% 1.81/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.81/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_14,plain,
% 1.81/0.99      ( v2_struct_0(X0)
% 1.81/0.99      | ~ l1_struct_0(X0)
% 1.81/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.81/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_259,plain,
% 1.81/0.99      ( v2_struct_0(X0)
% 1.81/0.99      | ~ l1_struct_0(X0)
% 1.81/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_23,negated_conjecture,
% 1.81/0.99      ( ~ v2_struct_0(sK1) ),
% 1.81/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_277,plain,
% 1.81/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_259,c_23]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_278,plain,
% 1.81/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_277]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_280,plain,
% 1.81/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.81/0.99      inference(global_propositional_subsumption,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_278,c_22]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_796,plain,
% 1.81/0.99      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_280,c_287]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_812,plain,
% 1.81/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
% 1.81/0.99      inference(forward_subsumption_resolution,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_809,c_796]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1326,plain,
% 1.81/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_struct_0(sK0) ),
% 1.81/0.99      inference(light_normalisation,[status(thm)],[c_1064,c_812,c_974]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_1395,plain,
% 1.81/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 1.81/0.99      inference(demodulation,[status(thm)],[c_1325,c_1326]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_16,negated_conjecture,
% 1.81/0.99      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.81/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.81/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_15,plain,
% 1.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | ~ v1_funct_1(X0)
% 1.81/0.99      | ~ v2_funct_1(X0)
% 1.81/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.81/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.81/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_298,plain,
% 1.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.99      | ~ v1_funct_1(X0)
% 1.81/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.81/0.99      | k2_relset_1(X1,X2,X0) != X2
% 1.81/0.99      | sK2 != X0 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_299,plain,
% 1.81/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 1.81/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.81/0.99      | ~ v1_funct_1(sK2)
% 1.81/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_298]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_303,plain,
% 1.81/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.81/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 1.81/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.81/0.99      inference(global_propositional_subsumption,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_299,c_21]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_304,plain,
% 1.81/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 1.81/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.81/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.81/0.99      inference(renaming,[status(thm)],[c_303]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_487,plain,
% 1.81/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 1.81/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | sK2 != sK2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_304]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_597,plain,
% 1.81/0.99      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 1.81/0.99      | u1_struct_0(sK0) != X0
% 1.81/0.99      | u1_struct_0(sK1) != X1
% 1.81/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.81/0.99      | sK2 != sK2 ),
% 1.81/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_487]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_598,plain,
% 1.81/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.81/0.99      inference(unflattening,[status(thm)],[c_597]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_814,plain,
% 1.81/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 1.81/0.99      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 1.81/0.99      inference(light_normalisation,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_598,c_287,c_292,c_801]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_815,plain,
% 1.81/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 1.81/0.99      inference(equality_resolution_simp,[status(thm)],[c_814]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(c_847,plain,
% 1.81/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.81/0.99      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 1.81/0.99      inference(light_normalisation,
% 1.81/0.99                [status(thm)],
% 1.81/0.99                [c_16,c_287,c_292,c_815]) ).
% 1.81/0.99  
% 1.81/0.99  cnf(contradiction,plain,
% 1.81/0.99      ( $false ),
% 1.81/0.99      inference(minisat,[status(thm)],[c_1396,c_1395,c_847]) ).
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/0.99  
% 1.81/0.99  ------                               Statistics
% 1.81/0.99  
% 1.81/0.99  ------ General
% 1.81/0.99  
% 1.81/0.99  abstr_ref_over_cycles:                  0
% 1.81/0.99  abstr_ref_under_cycles:                 0
% 1.81/0.99  gc_basic_clause_elim:                   0
% 1.81/0.99  forced_gc_time:                         0
% 1.81/0.99  parsing_time:                           0.009
% 1.81/0.99  unif_index_cands_time:                  0.
% 1.81/0.99  unif_index_add_time:                    0.
% 1.81/0.99  orderings_time:                         0.
% 1.81/0.99  out_proof_time:                         0.011
% 1.81/0.99  total_time:                             0.101
% 1.81/0.99  num_of_symbols:                         53
% 1.81/0.99  num_of_terms:                           1571
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing
% 1.81/0.99  
% 1.81/0.99  num_of_splits:                          0
% 1.81/0.99  num_of_split_atoms:                     0
% 1.81/0.99  num_of_reused_defs:                     0
% 1.81/0.99  num_eq_ax_congr_red:                    9
% 1.81/0.99  num_of_sem_filtered_clauses:            1
% 1.81/0.99  num_of_subtypes:                        0
% 1.81/0.99  monotx_restored_types:                  0
% 1.81/0.99  sat_num_of_epr_types:                   0
% 1.81/0.99  sat_num_of_non_cyclic_types:            0
% 1.81/0.99  sat_guarded_non_collapsed_types:        0
% 1.81/0.99  num_pure_diseq_elim:                    0
% 1.81/0.99  simp_replaced_by:                       0
% 1.81/0.99  res_preprocessed:                       103
% 1.81/0.99  prep_upred:                             0
% 1.81/0.99  prep_unflattend:                        37
% 1.81/0.99  smt_new_axioms:                         0
% 1.81/0.99  pred_elim_cands:                        1
% 1.81/0.99  pred_elim:                              7
% 1.81/0.99  pred_elim_cl:                           8
% 1.81/0.99  pred_elim_cycles:                       9
% 1.81/0.99  merged_defs:                            0
% 1.81/0.99  merged_defs_ncl:                        0
% 1.81/0.99  bin_hyper_res:                          0
% 1.81/0.99  prep_cycles:                            4
% 1.81/0.99  pred_elim_time:                         0.009
% 1.81/0.99  splitting_time:                         0.
% 1.81/0.99  sem_filter_time:                        0.
% 1.81/0.99  monotx_time:                            0.
% 1.81/0.99  subtype_inf_time:                       0.
% 1.81/0.99  
% 1.81/0.99  ------ Problem properties
% 1.81/0.99  
% 1.81/0.99  clauses:                                17
% 1.81/0.99  conjectures:                            2
% 1.81/0.99  epr:                                    0
% 1.81/0.99  horn:                                   14
% 1.81/0.99  ground:                                 9
% 1.81/0.99  unary:                                  5
% 1.81/0.99  binary:                                 7
% 1.81/0.99  lits:                                   39
% 1.81/0.99  lits_eq:                                35
% 1.81/0.99  fd_pure:                                0
% 1.81/0.99  fd_pseudo:                              0
% 1.81/0.99  fd_cond:                                2
% 1.81/0.99  fd_pseudo_cond:                         0
% 1.81/0.99  ac_symbols:                             0
% 1.81/0.99  
% 1.81/0.99  ------ Propositional Solver
% 1.81/0.99  
% 1.81/0.99  prop_solver_calls:                      26
% 1.81/0.99  prop_fast_solver_calls:                 612
% 1.81/0.99  smt_solver_calls:                       0
% 1.81/0.99  smt_fast_solver_calls:                  0
% 1.81/0.99  prop_num_of_clauses:                    417
% 1.81/0.99  prop_preprocess_simplified:             2211
% 1.81/0.99  prop_fo_subsumed:                       4
% 1.81/0.99  prop_solver_time:                       0.
% 1.81/0.99  smt_solver_time:                        0.
% 1.81/0.99  smt_fast_solver_time:                   0.
% 1.81/0.99  prop_fast_solver_time:                  0.
% 1.81/0.99  prop_unsat_core_time:                   0.
% 1.81/0.99  
% 1.81/0.99  ------ QBF
% 1.81/0.99  
% 1.81/0.99  qbf_q_res:                              0
% 1.81/0.99  qbf_num_tautologies:                    0
% 1.81/0.99  qbf_prep_cycles:                        0
% 1.81/0.99  
% 1.81/0.99  ------ BMC1
% 1.81/0.99  
% 1.81/0.99  bmc1_current_bound:                     -1
% 1.81/0.99  bmc1_last_solved_bound:                 -1
% 1.81/0.99  bmc1_unsat_core_size:                   -1
% 1.81/0.99  bmc1_unsat_core_parents_size:           -1
% 1.81/0.99  bmc1_merge_next_fun:                    0
% 1.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.81/0.99  
% 1.81/0.99  ------ Instantiation
% 1.81/0.99  
% 1.81/0.99  inst_num_of_clauses:                    175
% 1.81/0.99  inst_num_in_passive:                    11
% 1.81/0.99  inst_num_in_active:                     114
% 1.81/0.99  inst_num_in_unprocessed:                50
% 1.81/0.99  inst_num_of_loops:                      120
% 1.81/0.99  inst_num_of_learning_restarts:          0
% 1.81/0.99  inst_num_moves_active_passive:          4
% 1.81/0.99  inst_lit_activity:                      0
% 1.81/0.99  inst_lit_activity_moves:                0
% 1.81/0.99  inst_num_tautologies:                   0
% 1.81/0.99  inst_num_prop_implied:                  0
% 1.81/0.99  inst_num_existing_simplified:           0
% 1.81/0.99  inst_num_eq_res_simplified:             0
% 1.81/0.99  inst_num_child_elim:                    0
% 1.81/0.99  inst_num_of_dismatching_blockings:      13
% 1.81/0.99  inst_num_of_non_proper_insts:           155
% 1.81/0.99  inst_num_of_duplicates:                 0
% 1.81/0.99  inst_inst_num_from_inst_to_res:         0
% 1.81/0.99  inst_dismatching_checking_time:         0.
% 1.81/0.99  
% 1.81/0.99  ------ Resolution
% 1.81/0.99  
% 1.81/0.99  res_num_of_clauses:                     0
% 1.81/0.99  res_num_in_passive:                     0
% 1.81/0.99  res_num_in_active:                      0
% 1.81/0.99  res_num_of_loops:                       107
% 1.81/0.99  res_forward_subset_subsumed:            35
% 1.81/0.99  res_backward_subset_subsumed:           2
% 1.81/0.99  res_forward_subsumed:                   0
% 1.81/0.99  res_backward_subsumed:                  0
% 1.81/0.99  res_forward_subsumption_resolution:     0
% 1.81/0.99  res_backward_subsumption_resolution:    0
% 1.81/0.99  res_clause_to_clause_subsumption:       30
% 1.81/0.99  res_orphan_elimination:                 0
% 1.81/0.99  res_tautology_del:                      32
% 1.81/0.99  res_num_eq_res_simplified:              1
% 1.81/0.99  res_num_sel_changes:                    0
% 1.81/0.99  res_moves_from_active_to_pass:          0
% 1.81/0.99  
% 1.81/0.99  ------ Superposition
% 1.81/0.99  
% 1.81/0.99  sup_time_total:                         0.
% 1.81/0.99  sup_time_generating:                    0.
% 1.81/0.99  sup_time_sim_full:                      0.
% 1.81/0.99  sup_time_sim_immed:                     0.
% 1.81/0.99  
% 1.81/0.99  sup_num_of_clauses:                     19
% 1.81/0.99  sup_num_in_active:                      16
% 1.81/0.99  sup_num_in_passive:                     3
% 1.81/0.99  sup_num_of_loops:                       22
% 1.81/0.99  sup_fw_superposition:                   0
% 1.81/0.99  sup_bw_superposition:                   1
% 1.81/0.99  sup_immediate_simplified:               2
% 1.81/0.99  sup_given_eliminated:                   0
% 1.81/0.99  comparisons_done:                       0
% 1.81/0.99  comparisons_avoided:                    0
% 1.81/0.99  
% 1.81/0.99  ------ Simplifications
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  sim_fw_subset_subsumed:                 1
% 1.81/0.99  sim_bw_subset_subsumed:                 1
% 1.81/0.99  sim_fw_subsumed:                        0
% 1.81/0.99  sim_bw_subsumed:                        0
% 1.81/0.99  sim_fw_subsumption_res:                 1
% 1.81/0.99  sim_bw_subsumption_res:                 0
% 1.81/0.99  sim_tautology_del:                      0
% 1.81/0.99  sim_eq_tautology_del:                   0
% 1.81/0.99  sim_eq_res_simp:                        1
% 1.81/0.99  sim_fw_demodulated:                     1
% 1.81/0.99  sim_bw_demodulated:                     5
% 1.81/0.99  sim_light_normalised:                   15
% 1.81/0.99  sim_joinable_taut:                      0
% 1.81/0.99  sim_joinable_simp:                      0
% 1.81/0.99  sim_ac_normalised:                      0
% 1.81/0.99  sim_smt_subsumption:                    0
% 1.81/0.99  
%------------------------------------------------------------------------------
