%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:41 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  270 (7671862 expanded)
%              Number of clauses        :  197 (2110681 expanded)
%              Number of leaves         :   20 (2141541 expanded)
%              Depth                    :   45
%              Number of atoms          :  949 (47752716 expanded)
%              Number of equality atoms :  518 (8800306 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2)
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).

fof(f76,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f65])).

fof(f82,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1159,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1169,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1615,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1159,c_1169])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1162,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1764,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1615,c_1162])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1766,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1615,c_29])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1158,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1616,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1158,c_1169])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1179,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1618,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1162,c_1179])).

cnf(c_1619,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1618,c_29,c_1615,c_1616])).

cnf(c_1767,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1766,c_1616,c_1619])).

cnf(c_1770,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1764,c_1767])).

cnf(c_1771,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1770,c_1616])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1173,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4257,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1173])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1180,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2313,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1771,c_1180])).

cnf(c_4258,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4257,c_2313])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1161,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1765,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1615,c_1161])).

cnf(c_1768,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1765,c_1767])).

cnf(c_1769,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1768,c_1616])).

cnf(c_5815,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4258,c_1769])).

cnf(c_5816,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5815])).

cnf(c_1853,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1767,c_1619])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1168,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4155,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_1168])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4413,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_37,c_40,c_1769,c_1771])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1167,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3288,plain,
    ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1167,c_1179])).

cnf(c_3954,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3288])).

cnf(c_4150,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3954,c_37,c_1769])).

cnf(c_4415,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_4413,c_4150])).

cnf(c_1160,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1183,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3424,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1183])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1560,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1645,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_1646,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1942,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1943,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_3693,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_39,c_40,c_1646,c_1943])).

cnf(c_4427,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4415,c_3693])).

cnf(c_4508,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4427,c_1168])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1181,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2246,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1181])).

cnf(c_1405,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2308,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_32,c_30,c_28,c_1405,c_1645,c_1942])).

cnf(c_4510,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4508,c_2308])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1324,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1325,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3107,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3108,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3107])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1171,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4343,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_1171])).

cnf(c_4430,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1167])).

cnf(c_4588,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4510,c_37,c_39,c_40,c_1325,c_1646,c_1769,c_1771,c_1943,c_3108,c_4343,c_4430])).

cnf(c_5829,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5816,c_4588])).

cnf(c_16,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_384,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_385,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1157,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_38,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_386,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1233,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1234,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_1241,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1242,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1263,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1264,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_1275,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1276,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_1438,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1157,c_37,c_38,c_39,c_386,c_1234,c_1242,c_1264,c_1276])).

cnf(c_1439,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1438])).

cnf(c_1763,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1615,c_1439])).

cnf(c_1772,plain,
    ( k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),u1_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1763,c_1767])).

cnf(c_1773,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1772,c_1616])).

cnf(c_4421,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4413,c_1773])).

cnf(c_6305,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5829,c_4421])).

cnf(c_7761,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5829,c_6305])).

cnf(c_7768,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7761,c_1771])).

cnf(c_7769,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7768])).

cnf(c_7773,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5829,c_7769])).

cnf(c_1166,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7772,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_7769])).

cnf(c_7833,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7773,c_37,c_39,c_40,c_1325,c_1646,c_1769,c_1771,c_1943,c_4343,c_4430,c_7772])).

cnf(c_7874,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7833,c_1771])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1177,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3549,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1167,c_1177])).

cnf(c_6547,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_3549])).

cnf(c_6686,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1167,c_6547])).

cnf(c_15624,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_6686])).

cnf(c_15633,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_15624])).

cnf(c_7866,plain,
    ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7833,c_4413])).

cnf(c_15634,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15633,c_7866])).

cnf(c_4431,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1166])).

cnf(c_4661,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4431,c_37,c_40,c_1769,c_1771,c_4343])).

cnf(c_7862,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7833,c_4661])).

cnf(c_4922,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4430,c_37,c_1769,c_1771])).

cnf(c_7861,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7833,c_4922])).

cnf(c_10457,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7861,c_6547])).

cnf(c_15817,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15634,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7862,c_10457])).

cnf(c_15818,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15817])).

cnf(c_7860,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7833,c_4421])).

cnf(c_15840,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15818,c_7860])).

cnf(c_7875,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7833,c_1769])).

cnf(c_8637,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_1177])).

cnf(c_15860,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15840,c_7875,c_8637])).

cnf(c_15865,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15818,c_15860])).

cnf(c_15864,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1167,c_15860])).

cnf(c_15928,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15865,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7861,c_7862,c_15864])).

cnf(c_15929,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15928])).

cnf(c_15933,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15818,c_15929])).

cnf(c_15932,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_15929])).

cnf(c_15939,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15933,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7861,c_7862,c_15932])).

cnf(c_15964,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15939,c_7860])).

cnf(c_620,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_655,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_1477,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_621,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1973,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1974,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_1610,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1980,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_3435,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2188,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_3621,plain,
    ( X0 = u1_struct_0(sK0)
    | X0 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_3622,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3621])).

cnf(c_4568,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2604,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4669,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_4670,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4669])).

cnf(c_633,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1400,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK2,X3,X4)
    | X3 != X1
    | X4 != X2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_1576,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | v1_funct_2(sK2,X2,X3)
    | X2 != X0
    | X3 != X1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1693,plain,
    ( v1_funct_2(sK2,X0,X1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X1 != u1_struct_0(sK1)
    | X0 != u1_struct_0(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_5069,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),X0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X0 != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_5070,plain,
    ( X0 != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK2 != sK2
    | v1_funct_2(sK2,u1_struct_0(sK0),X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5069])).

cnf(c_5072,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK2 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5070])).

cnf(c_5340,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5341,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1) != iProver_top
    | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5340])).

cnf(c_5343,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5341])).

cnf(c_6538,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_6539,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6538])).

cnf(c_1851,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1767,c_1615])).

cnf(c_7876,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7833,c_1851])).

cnf(c_2609,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(sK2),X3,X4)
    | X3 != X1
    | X4 != X2
    | k2_funct_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_4676,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
    | v1_funct_2(k2_funct_1(sK2),X2,X3)
    | X2 != X0
    | X3 != X1
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_8898,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4676])).

cnf(c_8899,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | k2_funct_1(sK2) != k2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),X0,X1) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8898])).

cnf(c_8901,plain,
    ( k2_funct_1(sK2) != k2_funct_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8899])).

cnf(c_11003,plain,
    ( v1_funct_2(sK2,X0,X1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),X2)
    | X1 != X2
    | X0 != u1_struct_0(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_11012,plain,
    ( X0 != X1
    | X2 != u1_struct_0(sK0)
    | sK2 != sK2
    | v1_funct_2(sK2,X2,X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11003])).

cnf(c_11014,plain,
    ( sK2 != sK2
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11012])).

cnf(c_15966,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15939,c_7861])).

cnf(c_7863,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7833,c_4588])).

cnf(c_15977,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15939,c_7863])).

cnf(c_15978,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15939,c_7874])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1174,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16406,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15978,c_1174])).

cnf(c_7868,plain,
    ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7833,c_2313])).

cnf(c_15967,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_15939,c_7868])).

cnf(c_16411,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16406,c_15967])).

cnf(c_17791,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15964,c_37,c_38,c_39,c_29,c_40,c_655,c_1325,c_1477,c_1615,c_1616,c_1646,c_1943,c_1974,c_1980,c_3435,c_3622,c_4568,c_4670,c_5072,c_5343,c_6539,c_7861,c_7862,c_7876,c_8901,c_11014,c_15932,c_15966,c_15977,c_16411])).

cnf(c_16689,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15977,c_37,c_38,c_39,c_40,c_655,c_1325,c_1477,c_1616,c_1646,c_1943,c_1974,c_3435,c_3622,c_5072,c_6539,c_7861,c_7862,c_7876,c_11014,c_15932,c_16411])).

cnf(c_17795,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17791,c_16689])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17795,c_15932,c_11014,c_7876,c_7862,c_7861,c_6539,c_5072,c_3622,c_3435,c_1974,c_1943,c_1646,c_1616,c_1477,c_1325,c_655,c_40,c_39,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 7.58/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.50  
% 7.58/1.50  ------  iProver source info
% 7.58/1.50  
% 7.58/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.50  git: non_committed_changes: false
% 7.58/1.50  git: last_make_outside_of_git: false
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options
% 7.58/1.50  
% 7.58/1.50  --out_options                           all
% 7.58/1.50  --tptp_safe_out                         true
% 7.58/1.50  --problem_path                          ""
% 7.58/1.50  --include_path                          ""
% 7.58/1.50  --clausifier                            res/vclausify_rel
% 7.58/1.50  --clausifier_options                    ""
% 7.58/1.50  --stdin                                 false
% 7.58/1.50  --stats_out                             all
% 7.58/1.50  
% 7.58/1.50  ------ General Options
% 7.58/1.50  
% 7.58/1.50  --fof                                   false
% 7.58/1.50  --time_out_real                         305.
% 7.58/1.50  --time_out_virtual                      -1.
% 7.58/1.50  --symbol_type_check                     false
% 7.58/1.50  --clausify_out                          false
% 7.58/1.50  --sig_cnt_out                           false
% 7.58/1.50  --trig_cnt_out                          false
% 7.58/1.50  --trig_cnt_out_tolerance                1.
% 7.58/1.50  --trig_cnt_out_sk_spl                   false
% 7.58/1.50  --abstr_cl_out                          false
% 7.58/1.50  
% 7.58/1.50  ------ Global Options
% 7.58/1.50  
% 7.58/1.50  --schedule                              default
% 7.58/1.50  --add_important_lit                     false
% 7.58/1.50  --prop_solver_per_cl                    1000
% 7.58/1.50  --min_unsat_core                        false
% 7.58/1.50  --soft_assumptions                      false
% 7.58/1.50  --soft_lemma_size                       3
% 7.58/1.50  --prop_impl_unit_size                   0
% 7.58/1.50  --prop_impl_unit                        []
% 7.58/1.50  --share_sel_clauses                     true
% 7.58/1.50  --reset_solvers                         false
% 7.58/1.50  --bc_imp_inh                            [conj_cone]
% 7.58/1.50  --conj_cone_tolerance                   3.
% 7.58/1.50  --extra_neg_conj                        none
% 7.58/1.50  --large_theory_mode                     true
% 7.58/1.50  --prolific_symb_bound                   200
% 7.58/1.50  --lt_threshold                          2000
% 7.58/1.50  --clause_weak_htbl                      true
% 7.58/1.50  --gc_record_bc_elim                     false
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing Options
% 7.58/1.50  
% 7.58/1.50  --preprocessing_flag                    true
% 7.58/1.50  --time_out_prep_mult                    0.1
% 7.58/1.50  --splitting_mode                        input
% 7.58/1.50  --splitting_grd                         true
% 7.58/1.50  --splitting_cvd                         false
% 7.58/1.50  --splitting_cvd_svl                     false
% 7.58/1.50  --splitting_nvd                         32
% 7.58/1.50  --sub_typing                            true
% 7.58/1.50  --prep_gs_sim                           true
% 7.58/1.50  --prep_unflatten                        true
% 7.58/1.50  --prep_res_sim                          true
% 7.58/1.50  --prep_upred                            true
% 7.58/1.50  --prep_sem_filter                       exhaustive
% 7.58/1.50  --prep_sem_filter_out                   false
% 7.58/1.50  --pred_elim                             true
% 7.58/1.50  --res_sim_input                         true
% 7.58/1.50  --eq_ax_congr_red                       true
% 7.58/1.50  --pure_diseq_elim                       true
% 7.58/1.50  --brand_transform                       false
% 7.58/1.50  --non_eq_to_eq                          false
% 7.58/1.50  --prep_def_merge                        true
% 7.58/1.50  --prep_def_merge_prop_impl              false
% 7.58/1.50  --prep_def_merge_mbd                    true
% 7.58/1.50  --prep_def_merge_tr_red                 false
% 7.58/1.50  --prep_def_merge_tr_cl                  false
% 7.58/1.50  --smt_preprocessing                     true
% 7.58/1.50  --smt_ac_axioms                         fast
% 7.58/1.50  --preprocessed_out                      false
% 7.58/1.50  --preprocessed_stats                    false
% 7.58/1.50  
% 7.58/1.50  ------ Abstraction refinement Options
% 7.58/1.50  
% 7.58/1.50  --abstr_ref                             []
% 7.58/1.50  --abstr_ref_prep                        false
% 7.58/1.50  --abstr_ref_until_sat                   false
% 7.58/1.50  --abstr_ref_sig_restrict                funpre
% 7.58/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.50  --abstr_ref_under                       []
% 7.58/1.50  
% 7.58/1.50  ------ SAT Options
% 7.58/1.50  
% 7.58/1.50  --sat_mode                              false
% 7.58/1.50  --sat_fm_restart_options                ""
% 7.58/1.50  --sat_gr_def                            false
% 7.58/1.50  --sat_epr_types                         true
% 7.58/1.50  --sat_non_cyclic_types                  false
% 7.58/1.50  --sat_finite_models                     false
% 7.58/1.50  --sat_fm_lemmas                         false
% 7.58/1.50  --sat_fm_prep                           false
% 7.58/1.50  --sat_fm_uc_incr                        true
% 7.58/1.50  --sat_out_model                         small
% 7.58/1.50  --sat_out_clauses                       false
% 7.58/1.50  
% 7.58/1.50  ------ QBF Options
% 7.58/1.50  
% 7.58/1.50  --qbf_mode                              false
% 7.58/1.50  --qbf_elim_univ                         false
% 7.58/1.50  --qbf_dom_inst                          none
% 7.58/1.50  --qbf_dom_pre_inst                      false
% 7.58/1.50  --qbf_sk_in                             false
% 7.58/1.50  --qbf_pred_elim                         true
% 7.58/1.50  --qbf_split                             512
% 7.58/1.50  
% 7.58/1.50  ------ BMC1 Options
% 7.58/1.50  
% 7.58/1.50  --bmc1_incremental                      false
% 7.58/1.50  --bmc1_axioms                           reachable_all
% 7.58/1.50  --bmc1_min_bound                        0
% 7.58/1.50  --bmc1_max_bound                        -1
% 7.58/1.50  --bmc1_max_bound_default                -1
% 7.58/1.50  --bmc1_symbol_reachability              true
% 7.58/1.50  --bmc1_property_lemmas                  false
% 7.58/1.50  --bmc1_k_induction                      false
% 7.58/1.50  --bmc1_non_equiv_states                 false
% 7.58/1.50  --bmc1_deadlock                         false
% 7.58/1.50  --bmc1_ucm                              false
% 7.58/1.50  --bmc1_add_unsat_core                   none
% 7.58/1.50  --bmc1_unsat_core_children              false
% 7.58/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.50  --bmc1_out_stat                         full
% 7.58/1.50  --bmc1_ground_init                      false
% 7.58/1.50  --bmc1_pre_inst_next_state              false
% 7.58/1.50  --bmc1_pre_inst_state                   false
% 7.58/1.50  --bmc1_pre_inst_reach_state             false
% 7.58/1.50  --bmc1_out_unsat_core                   false
% 7.58/1.50  --bmc1_aig_witness_out                  false
% 7.58/1.50  --bmc1_verbose                          false
% 7.58/1.50  --bmc1_dump_clauses_tptp                false
% 7.58/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.50  --bmc1_dump_file                        -
% 7.58/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.50  --bmc1_ucm_extend_mode                  1
% 7.58/1.50  --bmc1_ucm_init_mode                    2
% 7.58/1.50  --bmc1_ucm_cone_mode                    none
% 7.58/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.50  --bmc1_ucm_relax_model                  4
% 7.58/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.50  --bmc1_ucm_layered_model                none
% 7.58/1.50  --bmc1_ucm_max_lemma_size               10
% 7.58/1.50  
% 7.58/1.50  ------ AIG Options
% 7.58/1.50  
% 7.58/1.50  --aig_mode                              false
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation Options
% 7.58/1.50  
% 7.58/1.50  --instantiation_flag                    true
% 7.58/1.50  --inst_sos_flag                         true
% 7.58/1.50  --inst_sos_phase                        true
% 7.58/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel_side                     num_symb
% 7.58/1.50  --inst_solver_per_active                1400
% 7.58/1.50  --inst_solver_calls_frac                1.
% 7.58/1.50  --inst_passive_queue_type               priority_queues
% 7.58/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.50  --inst_passive_queues_freq              [25;2]
% 7.58/1.50  --inst_dismatching                      true
% 7.58/1.50  --inst_eager_unprocessed_to_passive     true
% 7.58/1.50  --inst_prop_sim_given                   true
% 7.58/1.50  --inst_prop_sim_new                     false
% 7.58/1.50  --inst_subs_new                         false
% 7.58/1.50  --inst_eq_res_simp                      false
% 7.58/1.50  --inst_subs_given                       false
% 7.58/1.50  --inst_orphan_elimination               true
% 7.58/1.50  --inst_learning_loop_flag               true
% 7.58/1.50  --inst_learning_start                   3000
% 7.58/1.50  --inst_learning_factor                  2
% 7.58/1.50  --inst_start_prop_sim_after_learn       3
% 7.58/1.50  --inst_sel_renew                        solver
% 7.58/1.50  --inst_lit_activity_flag                true
% 7.58/1.50  --inst_restr_to_given                   false
% 7.58/1.50  --inst_activity_threshold               500
% 7.58/1.50  --inst_out_proof                        true
% 7.58/1.50  
% 7.58/1.50  ------ Resolution Options
% 7.58/1.50  
% 7.58/1.50  --resolution_flag                       true
% 7.58/1.50  --res_lit_sel                           adaptive
% 7.58/1.50  --res_lit_sel_side                      none
% 7.58/1.50  --res_ordering                          kbo
% 7.58/1.50  --res_to_prop_solver                    active
% 7.58/1.50  --res_prop_simpl_new                    false
% 7.58/1.50  --res_prop_simpl_given                  true
% 7.58/1.50  --res_passive_queue_type                priority_queues
% 7.58/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.50  --res_passive_queues_freq               [15;5]
% 7.58/1.50  --res_forward_subs                      full
% 7.58/1.50  --res_backward_subs                     full
% 7.58/1.50  --res_forward_subs_resolution           true
% 7.58/1.50  --res_backward_subs_resolution          true
% 7.58/1.50  --res_orphan_elimination                true
% 7.58/1.50  --res_time_limit                        2.
% 7.58/1.50  --res_out_proof                         true
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Options
% 7.58/1.50  
% 7.58/1.50  --superposition_flag                    true
% 7.58/1.50  --sup_passive_queue_type                priority_queues
% 7.58/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.50  --demod_completeness_check              fast
% 7.58/1.50  --demod_use_ground                      true
% 7.58/1.50  --sup_to_prop_solver                    passive
% 7.58/1.50  --sup_prop_simpl_new                    true
% 7.58/1.50  --sup_prop_simpl_given                  true
% 7.58/1.50  --sup_fun_splitting                     true
% 7.58/1.50  --sup_smt_interval                      50000
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Simplification Setup
% 7.58/1.50  
% 7.58/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.50  --sup_immed_triv                        [TrivRules]
% 7.58/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_bw_main                     []
% 7.58/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_input_bw                          []
% 7.58/1.50  
% 7.58/1.50  ------ Combination Options
% 7.58/1.50  
% 7.58/1.50  --comb_res_mult                         3
% 7.58/1.50  --comb_sup_mult                         2
% 7.58/1.50  --comb_inst_mult                        10
% 7.58/1.50  
% 7.58/1.50  ------ Debug Options
% 7.58/1.50  
% 7.58/1.50  --dbg_backtrace                         false
% 7.58/1.50  --dbg_dump_prop_clauses                 false
% 7.58/1.50  --dbg_dump_prop_clauses_file            -
% 7.58/1.50  --dbg_out_stat                          false
% 7.58/1.50  ------ Parsing...
% 7.58/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.50  ------ Proving...
% 7.58/1.50  ------ Problem Properties 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  clauses                                 33
% 7.58/1.50  conjectures                             7
% 7.58/1.50  EPR                                     4
% 7.58/1.50  Horn                                    29
% 7.58/1.50  unary                                   8
% 7.58/1.50  binary                                  3
% 7.58/1.50  lits                                    110
% 7.58/1.50  lits eq                                 23
% 7.58/1.50  fd_pure                                 0
% 7.58/1.50  fd_pseudo                               0
% 7.58/1.50  fd_cond                                 3
% 7.58/1.50  fd_pseudo_cond                          0
% 7.58/1.50  AC symbols                              0
% 7.58/1.50  
% 7.58/1.50  ------ Schedule dynamic 5 is on 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  Current options:
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options
% 7.58/1.50  
% 7.58/1.50  --out_options                           all
% 7.58/1.50  --tptp_safe_out                         true
% 7.58/1.50  --problem_path                          ""
% 7.58/1.50  --include_path                          ""
% 7.58/1.50  --clausifier                            res/vclausify_rel
% 7.58/1.50  --clausifier_options                    ""
% 7.58/1.50  --stdin                                 false
% 7.58/1.50  --stats_out                             all
% 7.58/1.50  
% 7.58/1.50  ------ General Options
% 7.58/1.50  
% 7.58/1.50  --fof                                   false
% 7.58/1.50  --time_out_real                         305.
% 7.58/1.50  --time_out_virtual                      -1.
% 7.58/1.50  --symbol_type_check                     false
% 7.58/1.50  --clausify_out                          false
% 7.58/1.50  --sig_cnt_out                           false
% 7.58/1.50  --trig_cnt_out                          false
% 7.58/1.50  --trig_cnt_out_tolerance                1.
% 7.58/1.50  --trig_cnt_out_sk_spl                   false
% 7.58/1.50  --abstr_cl_out                          false
% 7.58/1.50  
% 7.58/1.50  ------ Global Options
% 7.58/1.50  
% 7.58/1.50  --schedule                              default
% 7.58/1.50  --add_important_lit                     false
% 7.58/1.50  --prop_solver_per_cl                    1000
% 7.58/1.50  --min_unsat_core                        false
% 7.58/1.50  --soft_assumptions                      false
% 7.58/1.50  --soft_lemma_size                       3
% 7.58/1.50  --prop_impl_unit_size                   0
% 7.58/1.50  --prop_impl_unit                        []
% 7.58/1.50  --share_sel_clauses                     true
% 7.58/1.50  --reset_solvers                         false
% 7.58/1.50  --bc_imp_inh                            [conj_cone]
% 7.58/1.50  --conj_cone_tolerance                   3.
% 7.58/1.50  --extra_neg_conj                        none
% 7.58/1.50  --large_theory_mode                     true
% 7.58/1.50  --prolific_symb_bound                   200
% 7.58/1.50  --lt_threshold                          2000
% 7.58/1.50  --clause_weak_htbl                      true
% 7.58/1.50  --gc_record_bc_elim                     false
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing Options
% 7.58/1.50  
% 7.58/1.50  --preprocessing_flag                    true
% 7.58/1.50  --time_out_prep_mult                    0.1
% 7.58/1.50  --splitting_mode                        input
% 7.58/1.50  --splitting_grd                         true
% 7.58/1.50  --splitting_cvd                         false
% 7.58/1.50  --splitting_cvd_svl                     false
% 7.58/1.50  --splitting_nvd                         32
% 7.58/1.50  --sub_typing                            true
% 7.58/1.50  --prep_gs_sim                           true
% 7.58/1.50  --prep_unflatten                        true
% 7.58/1.50  --prep_res_sim                          true
% 7.58/1.50  --prep_upred                            true
% 7.58/1.50  --prep_sem_filter                       exhaustive
% 7.58/1.50  --prep_sem_filter_out                   false
% 7.58/1.50  --pred_elim                             true
% 7.58/1.50  --res_sim_input                         true
% 7.58/1.50  --eq_ax_congr_red                       true
% 7.58/1.50  --pure_diseq_elim                       true
% 7.58/1.50  --brand_transform                       false
% 7.58/1.50  --non_eq_to_eq                          false
% 7.58/1.50  --prep_def_merge                        true
% 7.58/1.50  --prep_def_merge_prop_impl              false
% 7.58/1.50  --prep_def_merge_mbd                    true
% 7.58/1.50  --prep_def_merge_tr_red                 false
% 7.58/1.50  --prep_def_merge_tr_cl                  false
% 7.58/1.50  --smt_preprocessing                     true
% 7.58/1.50  --smt_ac_axioms                         fast
% 7.58/1.50  --preprocessed_out                      false
% 7.58/1.50  --preprocessed_stats                    false
% 7.58/1.50  
% 7.58/1.50  ------ Abstraction refinement Options
% 7.58/1.50  
% 7.58/1.50  --abstr_ref                             []
% 7.58/1.50  --abstr_ref_prep                        false
% 7.58/1.50  --abstr_ref_until_sat                   false
% 7.58/1.50  --abstr_ref_sig_restrict                funpre
% 7.58/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.50  --abstr_ref_under                       []
% 7.58/1.50  
% 7.58/1.50  ------ SAT Options
% 7.58/1.50  
% 7.58/1.50  --sat_mode                              false
% 7.58/1.50  --sat_fm_restart_options                ""
% 7.58/1.50  --sat_gr_def                            false
% 7.58/1.50  --sat_epr_types                         true
% 7.58/1.50  --sat_non_cyclic_types                  false
% 7.58/1.50  --sat_finite_models                     false
% 7.58/1.50  --sat_fm_lemmas                         false
% 7.58/1.50  --sat_fm_prep                           false
% 7.58/1.50  --sat_fm_uc_incr                        true
% 7.58/1.50  --sat_out_model                         small
% 7.58/1.50  --sat_out_clauses                       false
% 7.58/1.50  
% 7.58/1.50  ------ QBF Options
% 7.58/1.50  
% 7.58/1.50  --qbf_mode                              false
% 7.58/1.50  --qbf_elim_univ                         false
% 7.58/1.50  --qbf_dom_inst                          none
% 7.58/1.50  --qbf_dom_pre_inst                      false
% 7.58/1.50  --qbf_sk_in                             false
% 7.58/1.50  --qbf_pred_elim                         true
% 7.58/1.50  --qbf_split                             512
% 7.58/1.50  
% 7.58/1.50  ------ BMC1 Options
% 7.58/1.50  
% 7.58/1.50  --bmc1_incremental                      false
% 7.58/1.50  --bmc1_axioms                           reachable_all
% 7.58/1.50  --bmc1_min_bound                        0
% 7.58/1.50  --bmc1_max_bound                        -1
% 7.58/1.50  --bmc1_max_bound_default                -1
% 7.58/1.50  --bmc1_symbol_reachability              true
% 7.58/1.50  --bmc1_property_lemmas                  false
% 7.58/1.50  --bmc1_k_induction                      false
% 7.58/1.50  --bmc1_non_equiv_states                 false
% 7.58/1.50  --bmc1_deadlock                         false
% 7.58/1.50  --bmc1_ucm                              false
% 7.58/1.50  --bmc1_add_unsat_core                   none
% 7.58/1.50  --bmc1_unsat_core_children              false
% 7.58/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.50  --bmc1_out_stat                         full
% 7.58/1.50  --bmc1_ground_init                      false
% 7.58/1.50  --bmc1_pre_inst_next_state              false
% 7.58/1.50  --bmc1_pre_inst_state                   false
% 7.58/1.50  --bmc1_pre_inst_reach_state             false
% 7.58/1.50  --bmc1_out_unsat_core                   false
% 7.58/1.50  --bmc1_aig_witness_out                  false
% 7.58/1.50  --bmc1_verbose                          false
% 7.58/1.50  --bmc1_dump_clauses_tptp                false
% 7.58/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.50  --bmc1_dump_file                        -
% 7.58/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.50  --bmc1_ucm_extend_mode                  1
% 7.58/1.50  --bmc1_ucm_init_mode                    2
% 7.58/1.50  --bmc1_ucm_cone_mode                    none
% 7.58/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.50  --bmc1_ucm_relax_model                  4
% 7.58/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.50  --bmc1_ucm_layered_model                none
% 7.58/1.50  --bmc1_ucm_max_lemma_size               10
% 7.58/1.50  
% 7.58/1.50  ------ AIG Options
% 7.58/1.50  
% 7.58/1.50  --aig_mode                              false
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation Options
% 7.58/1.50  
% 7.58/1.50  --instantiation_flag                    true
% 7.58/1.50  --inst_sos_flag                         true
% 7.58/1.50  --inst_sos_phase                        true
% 7.58/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel_side                     none
% 7.58/1.50  --inst_solver_per_active                1400
% 7.58/1.50  --inst_solver_calls_frac                1.
% 7.58/1.50  --inst_passive_queue_type               priority_queues
% 7.58/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.50  --inst_passive_queues_freq              [25;2]
% 7.58/1.50  --inst_dismatching                      true
% 7.58/1.50  --inst_eager_unprocessed_to_passive     true
% 7.58/1.50  --inst_prop_sim_given                   true
% 7.58/1.50  --inst_prop_sim_new                     false
% 7.58/1.50  --inst_subs_new                         false
% 7.58/1.50  --inst_eq_res_simp                      false
% 7.58/1.50  --inst_subs_given                       false
% 7.58/1.50  --inst_orphan_elimination               true
% 7.58/1.50  --inst_learning_loop_flag               true
% 7.58/1.50  --inst_learning_start                   3000
% 7.58/1.50  --inst_learning_factor                  2
% 7.58/1.50  --inst_start_prop_sim_after_learn       3
% 7.58/1.50  --inst_sel_renew                        solver
% 7.58/1.50  --inst_lit_activity_flag                true
% 7.58/1.50  --inst_restr_to_given                   false
% 7.58/1.50  --inst_activity_threshold               500
% 7.58/1.50  --inst_out_proof                        true
% 7.58/1.50  
% 7.58/1.50  ------ Resolution Options
% 7.58/1.50  
% 7.58/1.50  --resolution_flag                       false
% 7.58/1.50  --res_lit_sel                           adaptive
% 7.58/1.50  --res_lit_sel_side                      none
% 7.58/1.50  --res_ordering                          kbo
% 7.58/1.50  --res_to_prop_solver                    active
% 7.58/1.50  --res_prop_simpl_new                    false
% 7.58/1.50  --res_prop_simpl_given                  true
% 7.58/1.50  --res_passive_queue_type                priority_queues
% 7.58/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.50  --res_passive_queues_freq               [15;5]
% 7.58/1.50  --res_forward_subs                      full
% 7.58/1.50  --res_backward_subs                     full
% 7.58/1.50  --res_forward_subs_resolution           true
% 7.58/1.50  --res_backward_subs_resolution          true
% 7.58/1.50  --res_orphan_elimination                true
% 7.58/1.50  --res_time_limit                        2.
% 7.58/1.50  --res_out_proof                         true
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Options
% 7.58/1.50  
% 7.58/1.50  --superposition_flag                    true
% 7.58/1.50  --sup_passive_queue_type                priority_queues
% 7.58/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.50  --demod_completeness_check              fast
% 7.58/1.50  --demod_use_ground                      true
% 7.58/1.50  --sup_to_prop_solver                    passive
% 7.58/1.50  --sup_prop_simpl_new                    true
% 7.58/1.50  --sup_prop_simpl_given                  true
% 7.58/1.50  --sup_fun_splitting                     true
% 7.58/1.50  --sup_smt_interval                      50000
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Simplification Setup
% 7.58/1.50  
% 7.58/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.50  --sup_immed_triv                        [TrivRules]
% 7.58/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_bw_main                     []
% 7.58/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_input_bw                          []
% 7.58/1.50  
% 7.58/1.50  ------ Combination Options
% 7.58/1.50  
% 7.58/1.50  --comb_res_mult                         3
% 7.58/1.50  --comb_sup_mult                         2
% 7.58/1.50  --comb_inst_mult                        10
% 7.58/1.50  
% 7.58/1.50  ------ Debug Options
% 7.58/1.50  
% 7.58/1.50  --dbg_backtrace                         false
% 7.58/1.50  --dbg_dump_prop_clauses                 false
% 7.58/1.50  --dbg_dump_prop_clauses_file            -
% 7.58/1.50  --dbg_out_stat                          false
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ Proving...
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS status Theorem for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  fof(f15,conjecture,(
% 7.58/1.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f16,negated_conjecture,(
% 7.58/1.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.58/1.50    inference(negated_conjecture,[],[f15])).
% 7.58/1.50  
% 7.58/1.50  fof(f17,plain,(
% 7.58/1.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.58/1.50    inference(pure_predicate_removal,[],[f16])).
% 7.58/1.50  
% 7.58/1.50  fof(f40,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f17])).
% 7.58/1.50  
% 7.58/1.50  fof(f41,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 7.58/1.50    inference(flattening,[],[f40])).
% 7.58/1.50  
% 7.58/1.50  fof(f46,plain,(
% 7.58/1.50    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f45,plain,(
% 7.58/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f44,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f47,plain,(
% 7.58/1.50    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 7.58/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).
% 7.58/1.50  
% 7.58/1.50  fof(f76,plain,(
% 7.58/1.50    l1_struct_0(sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f11,axiom,(
% 7.58/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f33,plain,(
% 7.58/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f69,plain,(
% 7.58/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f33])).
% 7.58/1.50  
% 7.58/1.50  fof(f79,plain,(
% 7.58/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f80,plain,(
% 7.58/1.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f75,plain,(
% 7.58/1.50    l1_struct_0(sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f7,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f26,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f7])).
% 7.58/1.50  
% 7.58/1.50  fof(f57,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f26])).
% 7.58/1.50  
% 7.58/1.50  fof(f8,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f27,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f8])).
% 7.58/1.50  
% 7.58/1.50  fof(f28,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(flattening,[],[f27])).
% 7.58/1.50  
% 7.58/1.50  fof(f42,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(nnf_transformation,[],[f28])).
% 7.58/1.50  
% 7.58/1.50  fof(f58,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f6,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f25,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f6])).
% 7.58/1.50  
% 7.58/1.50  fof(f56,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f78,plain,(
% 7.58/1.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f12,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f34,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f12])).
% 7.58/1.50  
% 7.58/1.50  fof(f35,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f34])).
% 7.58/1.50  
% 7.58/1.50  fof(f70,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f77,plain,(
% 7.58/1.50    v1_funct_1(sK2)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f81,plain,(
% 7.58/1.50    v2_funct_1(sK2)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f13,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f36,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f13])).
% 7.58/1.50  
% 7.58/1.50  fof(f37,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f36])).
% 7.58/1.50  
% 7.58/1.50  fof(f73,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f37])).
% 7.58/1.50  
% 7.58/1.50  fof(f4,axiom,(
% 7.58/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f21,plain,(
% 7.58/1.50    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f4])).
% 7.58/1.50  
% 7.58/1.50  fof(f22,plain,(
% 7.58/1.50    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(flattening,[],[f21])).
% 7.58/1.50  
% 7.58/1.50  fof(f54,plain,(
% 7.58/1.50    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f22])).
% 7.58/1.50  
% 7.58/1.50  fof(f1,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f18,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f1])).
% 7.58/1.50  
% 7.58/1.50  fof(f48,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f18])).
% 7.58/1.50  
% 7.58/1.50  fof(f2,axiom,(
% 7.58/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f49,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f2])).
% 7.58/1.50  
% 7.58/1.50  fof(f5,axiom,(
% 7.58/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f23,plain,(
% 7.58/1.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f5])).
% 7.58/1.50  
% 7.58/1.50  fof(f24,plain,(
% 7.58/1.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(flattening,[],[f23])).
% 7.58/1.50  
% 7.58/1.50  fof(f55,plain,(
% 7.58/1.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f24])).
% 7.58/1.50  
% 7.58/1.50  fof(f3,axiom,(
% 7.58/1.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f19,plain,(
% 7.58/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f3])).
% 7.58/1.50  
% 7.58/1.50  fof(f20,plain,(
% 7.58/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(flattening,[],[f19])).
% 7.58/1.50  
% 7.58/1.50  fof(f51,plain,(
% 7.58/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f52,plain,(
% 7.58/1.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f10,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f31,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f10])).
% 7.58/1.50  
% 7.58/1.50  fof(f32,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f31])).
% 7.58/1.50  
% 7.58/1.50  fof(f67,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f32])).
% 7.58/1.50  
% 7.58/1.50  fof(f9,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f29,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f9])).
% 7.58/1.50  
% 7.58/1.50  fof(f30,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f29])).
% 7.58/1.50  
% 7.58/1.50  fof(f43,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(nnf_transformation,[],[f30])).
% 7.58/1.50  
% 7.58/1.50  fof(f65,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f43])).
% 7.58/1.50  
% 7.58/1.50  fof(f88,plain,(
% 7.58/1.50    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.58/1.50    inference(equality_resolution,[],[f65])).
% 7.58/1.50  
% 7.58/1.50  fof(f82,plain,(
% 7.58/1.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f71,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f37])).
% 7.58/1.50  
% 7.58/1.50  fof(f72,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f37])).
% 7.58/1.50  
% 7.58/1.50  fof(f62,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f85,plain,(
% 7.58/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.58/1.50    inference(equality_resolution,[],[f62])).
% 7.58/1.50  
% 7.58/1.50  fof(f59,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f87,plain,(
% 7.58/1.50    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.58/1.50    inference(equality_resolution,[],[f59])).
% 7.58/1.50  
% 7.58/1.50  cnf(c_33,negated_conjecture,
% 7.58/1.50      ( l1_struct_0(sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1159,plain,
% 7.58/1.50      ( l1_struct_0(sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_21,plain,
% 7.58/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1169,plain,
% 7.58/1.50      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.58/1.50      | l1_struct_0(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1615,plain,
% 7.58/1.50      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1159,c_1169]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_30,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1162,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1764,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1615,c_1162]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_29,negated_conjecture,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1766,plain,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1615,c_29]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_34,negated_conjecture,
% 7.58/1.50      ( l1_struct_0(sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1158,plain,
% 7.58/1.50      ( l1_struct_0(sK0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1616,plain,
% 7.58/1.50      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1158,c_1169]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1179,plain,
% 7.58/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1618,plain,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1162,c_1179]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1619,plain,
% 7.58/1.50      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 7.58/1.50      inference(light_normalisation,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_1618,c_29,c_1615,c_1616]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1767,plain,
% 7.58/1.50      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_1766,c_1616,c_1619]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1770,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1764,c_1767]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1771,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_1770,c_1616]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.58/1.50      | k1_xboole_0 = X2 ),
% 7.58/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1173,plain,
% 7.58/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.58/1.50      | k1_xboole_0 = X1
% 7.58/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4257,plain,
% 7.58/1.50      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 7.58/1.50      | k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1771,c_1173]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1180,plain,
% 7.58/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2313,plain,
% 7.58/1.50      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1771,c_1180]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4258,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 7.58/1.50      | k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_4257,c_2313]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_31,negated_conjecture,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1161,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1765,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1615,c_1161]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1768,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1765,c_1767]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1769,plain,
% 7.58/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_1768,c_1616]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5815,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4258,c_1769]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5816,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 7.58/1.50      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_5815]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1853,plain,
% 7.58/1.50      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1767,c_1619]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_22,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 7.58/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.58/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1168,plain,
% 7.58/1.50      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 7.58/1.50      | k2_relset_1(X0,X1,X2) != X1
% 7.58/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top
% 7.58/1.50      | v2_funct_1(X2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4155,plain,
% 7.58/1.50      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1853,c_1168]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_32,negated_conjecture,
% 7.58/1.50      ( v1_funct_1(sK2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_37,plain,
% 7.58/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28,negated_conjecture,
% 7.58/1.50      ( v2_funct_1(sK2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_40,plain,
% 7.58/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4413,plain,
% 7.58/1.50      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4155,c_37,c_40,c_1769,c_1771]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_23,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.58/1.50      | ~ v1_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1167,plain,
% 7.58/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.58/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 7.58/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3288,plain,
% 7.58/1.50      ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
% 7.58/1.50      | v1_funct_2(X2,X1,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1167,c_1179]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3954,plain,
% 7.58/1.50      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1771,c_3288]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4150,plain,
% 7.58/1.50      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_3954,c_37,c_1769]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4415,plain,
% 7.58/1.50      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_4413,c_4150]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1160,plain,
% 7.58/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1183,plain,
% 7.58/1.50      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.58/1.50      | v1_funct_1(X0) != iProver_top
% 7.58/1.50      | v2_funct_1(X0) != iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3424,plain,
% 7.58/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top
% 7.58/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1160,c_1183]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_39,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_0,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | ~ v1_relat_1(X1)
% 7.58/1.50      | v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1391,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | v1_relat_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1560,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.58/1.50      | v1_relat_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1391]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1645,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 7.58/1.50      | v1_relat_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1560]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1646,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 7.58/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1,plain,
% 7.58/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1942,plain,
% 7.58/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1943,plain,
% 7.58/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3693,plain,
% 7.58/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_3424,c_39,c_40,c_1646,c_1943]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4427,plain,
% 7.58/1.50      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_4415,c_3693]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4508,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 7.58/1.50      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.58/1.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4427,c_1168]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1181,plain,
% 7.58/1.50      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.58/1.50      | v1_funct_1(X0) != iProver_top
% 7.58/1.50      | v2_funct_1(X0) != iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2246,plain,
% 7.58/1.50      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top
% 7.58/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1160,c_1181]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1405,plain,
% 7.58/1.50      ( ~ v1_funct_1(sK2)
% 7.58/1.50      | ~ v2_funct_1(sK2)
% 7.58/1.50      | ~ v1_relat_1(sK2)
% 7.58/1.50      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2308,plain,
% 7.58/1.50      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_2246,c_32,c_30,c_28,c_1405,c_1645,c_1942]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4510,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 7.58/1.50      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.58/1.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_4508,c_2308]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1324,plain,
% 7.58/1.50      ( v1_funct_1(k2_funct_1(sK2))
% 7.58/1.50      | ~ v1_funct_1(sK2)
% 7.58/1.50      | ~ v2_funct_1(sK2)
% 7.58/1.50      | ~ v1_relat_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1325,plain,
% 7.58/1.50      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top
% 7.58/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | v2_funct_1(k2_funct_1(X0))
% 7.58/1.50      | ~ v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3107,plain,
% 7.58/1.50      ( ~ v1_funct_1(sK2)
% 7.58/1.50      | v2_funct_1(k2_funct_1(sK2))
% 7.58/1.50      | ~ v2_funct_1(sK2)
% 7.58/1.50      | ~ v1_relat_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3108,plain,
% 7.58/1.50      ( v1_funct_1(sK2) != iProver_top
% 7.58/1.50      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top
% 7.58/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_3107]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.58/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1171,plain,
% 7.58/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.58/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top
% 7.58/1.50      | v2_funct_1(X2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4343,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1853,c_1171]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4430,plain,
% 7.58/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4413,c_1167]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4588,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 7.58/1.50      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4510,c_37,c_39,c_40,c_1325,c_1646,c_1769,c_1771,
% 7.58/1.50                 c_1943,c_3108,c_4343,c_4430]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5829,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 7.58/1.50      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5816,c_4588]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16,plain,
% 7.58/1.50      ( r2_funct_2(X0,X1,X2,X2)
% 7.58/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ v1_funct_1(X2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27,negated_conjecture,
% 7.58/1.50      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_384,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 7.58/1.50      | u1_struct_0(sK1) != X2
% 7.58/1.50      | u1_struct_0(sK0) != X1
% 7.58/1.50      | sK2 != X0 ),
% 7.58/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_385,plain,
% 7.58/1.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 7.58/1.50      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 7.58/1.50      inference(unflattening,[status(thm)],[c_384]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1157,plain,
% 7.58/1.50      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 7.58/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_38,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_386,plain,
% 7.58/1.50      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 7.58/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1233,plain,
% 7.58/1.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 7.58/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 7.58/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1234,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1241,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 7.58/1.50      | ~ v1_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1242,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_24,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1263,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 7.58/1.50      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | ~ v1_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_24]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1264,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1275,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | ~ v1_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1276,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1438,plain,
% 7.58/1.50      ( m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_1157,c_37,c_38,c_39,c_386,c_1234,c_1242,c_1264,c_1276]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1439,plain,
% 7.58/1.50      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 7.58/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_1438]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1763,plain,
% 7.58/1.50      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1615,c_1439]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1772,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),u1_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1763,c_1767]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1773,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_1772,c_1616]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4421,plain,
% 7.58/1.50      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_4413,c_1773]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6305,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5829,c_4421]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7761,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5829,c_6305]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7768,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_7761,c_1771]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7769,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_7768]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7773,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5829,c_7769]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1166,plain,
% 7.58/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 7.58/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7772,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1166,c_7769]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7833,plain,
% 7.58/1.50      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_7773,c_37,c_39,c_40,c_1325,c_1646,c_1769,c_1771,
% 7.58/1.50                 c_1943,c_4343,c_4430,c_7772]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7874,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_1771]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.58/1.50      | k1_xboole_0 = X1
% 7.58/1.50      | k1_xboole_0 = X0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1177,plain,
% 7.58/1.50      ( k1_xboole_0 = X0
% 7.58/1.50      | k1_xboole_0 = X1
% 7.58/1.50      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3549,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = X0
% 7.58/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1167,c_1177]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6547,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = X0
% 7.58/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1166,c_3549]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6686,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = X0
% 7.58/1.50      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1167,c_6547]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15624,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = X0
% 7.58/1.50      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1166,c_6686]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15633,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)) = k1_xboole_0
% 7.58/1.50      | k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_7874,c_15624]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7866,plain,
% 7.58/1.50      ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_4413]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15634,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
% 7.58/1.50      | k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_15633,c_7866]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4431,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4413,c_1166]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4661,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4431,c_37,c_40,c_1769,c_1771,c_4343]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7862,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_4661]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4922,plain,
% 7.58/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4430,c_37,c_1769,c_1771]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7861,plain,
% 7.58/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_4922]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10457,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
% 7.58/1.50      | k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_7861,c_6547]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15817,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15634,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7862,
% 7.58/1.50                 c_10457]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15818,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
% 7.58/1.50      | k2_struct_0(sK0) = k1_xboole_0 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_15817]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7860,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_4421]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15840,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | sK2 != k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15818,c_7860]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7875,plain,
% 7.58/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_1769]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8637,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | sK2 = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_7874,c_1177]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15860,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15840,c_7875,c_8637]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15865,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15818,c_15860]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15864,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1167,c_15860]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15928,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | k2_struct_0(sK0) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15865,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7861,
% 7.58/1.50                 c_7862,c_15864]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15929,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_15928]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15933,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15818,c_15929]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15932,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1166,c_15929]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15939,plain,
% 7.58/1.50      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15933,c_37,c_39,c_40,c_1325,c_1646,c_1943,c_7861,
% 7.58/1.50                 c_7862,c_15932]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15964,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != sK2
% 7.58/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_15939,c_7860]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_620,plain,( X0 = X0 ),theory(equality) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_655,plain,
% 7.58/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_620]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1477,plain,
% 7.58/1.50      ( sK2 = sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_620]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_621,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1973,plain,
% 7.58/1.50      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1974,plain,
% 7.58/1.50      ( u1_struct_0(sK1) != k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = u1_struct_0(sK1)
% 7.58/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1973]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1610,plain,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 7.58/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 7.58/1.50      | u1_struct_0(sK1) != X0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1980,plain,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 7.58/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 7.58/1.50      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1610]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3435,plain,
% 7.58/1.50      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_620]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2188,plain,
% 7.58/1.50      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3621,plain,
% 7.58/1.50      ( X0 = u1_struct_0(sK0)
% 7.58/1.50      | X0 != k2_struct_0(sK0)
% 7.58/1.50      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2188]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3622,plain,
% 7.58/1.50      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 7.58/1.50      | k1_xboole_0 = u1_struct_0(sK0)
% 7.58/1.50      | k1_xboole_0 != k2_struct_0(sK0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4568,plain,
% 7.58/1.50      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_620]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2604,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.58/1.50      | ~ v1_funct_2(sK2,X1,X0)
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.58/1.50      | ~ v1_funct_1(sK2)
% 7.58/1.50      | ~ v2_funct_1(sK2)
% 7.58/1.50      | k2_relset_1(X1,X0,sK2) != X0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4669,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 7.58/1.50      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.58/1.50      | ~ v1_funct_1(sK2)
% 7.58/1.50      | ~ v2_funct_1(sK2)
% 7.58/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2604]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4670,plain,
% 7.58/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK2) != iProver_top
% 7.58/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_4669]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_633,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_funct_2(X3,X4,X5)
% 7.58/1.50      | X3 != X0
% 7.58/1.50      | X4 != X1
% 7.58/1.50      | X5 != X2 ),
% 7.58/1.50      theory(equality) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1400,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_funct_2(sK2,X3,X4)
% 7.58/1.50      | X3 != X1
% 7.58/1.50      | X4 != X2
% 7.58/1.50      | sK2 != X0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_633]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1576,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.58/1.50      | v1_funct_2(sK2,X2,X3)
% 7.58/1.50      | X2 != X0
% 7.58/1.50      | X3 != X1
% 7.58/1.50      | sK2 != sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1400]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1693,plain,
% 7.58/1.50      ( v1_funct_2(sK2,X0,X1)
% 7.58/1.50      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | X1 != u1_struct_0(sK1)
% 7.58/1.50      | X0 != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5069,plain,
% 7.58/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),X0)
% 7.58/1.50      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.58/1.50      | X0 != u1_struct_0(sK1)
% 7.58/1.50      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1693]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5070,plain,
% 7.58/1.50      ( X0 != u1_struct_0(sK1)
% 7.58/1.50      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),X0) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_5069]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5072,plain,
% 7.58/1.50      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2
% 7.58/1.50      | k1_xboole_0 != u1_struct_0(sK1)
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_5070]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5340,plain,
% 7.58/1.50      ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.58/1.50      | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.58/1.50      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5341,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),X0,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_5340]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5343,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_5341]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6538,plain,
% 7.58/1.50      ( X0 != X1 | X0 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6539,plain,
% 7.58/1.50      ( k2_struct_0(sK0) != k1_xboole_0
% 7.58/1.50      | k1_xboole_0 = k2_struct_0(sK0)
% 7.58/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_6538]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1851,plain,
% 7.58/1.50      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_1767,c_1615]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7876,plain,
% 7.58/1.50      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_1851]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2609,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),X3,X4)
% 7.58/1.50      | X3 != X1
% 7.58/1.50      | X4 != X2
% 7.58/1.50      | k2_funct_1(sK2) != X0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_633]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4676,plain,
% 7.58/1.50      ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),X2,X3)
% 7.58/1.50      | X2 != X0
% 7.58/1.50      | X3 != X1
% 7.58/1.50      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2609]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8898,plain,
% 7.58/1.50      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.58/1.50      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 7.58/1.50      | X0 != u1_struct_0(sK1)
% 7.58/1.50      | X1 != u1_struct_0(sK0)
% 7.58/1.50      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_4676]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8899,plain,
% 7.58/1.50      ( X0 != u1_struct_0(sK1)
% 7.58/1.50      | X1 != u1_struct_0(sK0)
% 7.58/1.50      | k2_funct_1(sK2) != k2_funct_1(sK2)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),X0,X1) = iProver_top
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_8898]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8901,plain,
% 7.58/1.50      ( k2_funct_1(sK2) != k2_funct_1(sK2)
% 7.58/1.50      | k1_xboole_0 != u1_struct_0(sK1)
% 7.58/1.50      | k1_xboole_0 != u1_struct_0(sK0)
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_8899]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11003,plain,
% 7.58/1.50      ( v1_funct_2(sK2,X0,X1)
% 7.58/1.50      | ~ v1_funct_2(sK2,u1_struct_0(sK0),X2)
% 7.58/1.50      | X1 != X2
% 7.58/1.50      | X0 != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11012,plain,
% 7.58/1.50      ( X0 != X1
% 7.58/1.50      | X2 != u1_struct_0(sK0)
% 7.58/1.50      | sK2 != sK2
% 7.58/1.50      | v1_funct_2(sK2,X2,X0) = iProver_top
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),X1) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_11003]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11014,plain,
% 7.58/1.50      ( sK2 != sK2
% 7.58/1.50      | k1_xboole_0 != u1_struct_0(sK0)
% 7.58/1.50      | k1_xboole_0 != k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_11012]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15966,plain,
% 7.58/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_15939,c_7861]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7863,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 7.58/1.50      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_4588]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15977,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
% 7.58/1.50      | k1_relat_1(sK2) != k1_xboole_0 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_15939,c_7863]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15978,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_15939,c_7874]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.58/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1174,plain,
% 7.58/1.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16406,plain,
% 7.58/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15978,c_1174]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7868,plain,
% 7.58/1.50      ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_7833,c_2313]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15967,plain,
% 7.58/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_15939,c_7868]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16411,plain,
% 7.58/1.50      ( k1_relat_1(sK2) = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_16406,c_15967]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17791,plain,
% 7.58/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15964,c_37,c_38,c_39,c_29,c_40,c_655,c_1325,c_1477,
% 7.58/1.50                 c_1615,c_1616,c_1646,c_1943,c_1974,c_1980,c_3435,c_3622,
% 7.58/1.50                 c_4568,c_4670,c_5072,c_5343,c_6539,c_7861,c_7862,c_7876,
% 7.58/1.50                 c_8901,c_11014,c_15932,c_15966,c_15977,c_16411]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16689,plain,
% 7.58/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_15977,c_37,c_38,c_39,c_40,c_655,c_1325,c_1477,c_1616,
% 7.58/1.50                 c_1646,c_1943,c_1974,c_3435,c_3622,c_5072,c_6539,c_7861,
% 7.58/1.50                 c_7862,c_7876,c_11014,c_15932,c_16411]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17795,plain,
% 7.58/1.50      ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_17791,c_16689]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(contradiction,plain,
% 7.58/1.50      ( $false ),
% 7.58/1.50      inference(minisat,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17795,c_15932,c_11014,c_7876,c_7862,c_7861,c_6539,
% 7.58/1.50                 c_5072,c_3622,c_3435,c_1974,c_1943,c_1646,c_1616,c_1477,
% 7.58/1.50                 c_1325,c_655,c_40,c_39,c_38,c_37]) ).
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  ------                               Statistics
% 7.58/1.50  
% 7.58/1.50  ------ General
% 7.58/1.50  
% 7.58/1.50  abstr_ref_over_cycles:                  0
% 7.58/1.50  abstr_ref_under_cycles:                 0
% 7.58/1.50  gc_basic_clause_elim:                   0
% 7.58/1.50  forced_gc_time:                         0
% 7.58/1.50  parsing_time:                           0.017
% 7.58/1.50  unif_index_cands_time:                  0.
% 7.58/1.50  unif_index_add_time:                    0.
% 7.58/1.50  orderings_time:                         0.
% 7.58/1.50  out_proof_time:                         0.02
% 7.58/1.50  total_time:                             0.64
% 7.58/1.50  num_of_symbols:                         52
% 7.58/1.50  num_of_terms:                           19025
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing
% 7.58/1.50  
% 7.58/1.50  num_of_splits:                          0
% 7.58/1.50  num_of_split_atoms:                     0
% 7.58/1.50  num_of_reused_defs:                     0
% 7.58/1.50  num_eq_ax_congr_red:                    6
% 7.58/1.50  num_of_sem_filtered_clauses:            1
% 7.58/1.50  num_of_subtypes:                        0
% 7.58/1.50  monotx_restored_types:                  0
% 7.58/1.50  sat_num_of_epr_types:                   0
% 7.58/1.50  sat_num_of_non_cyclic_types:            0
% 7.58/1.50  sat_guarded_non_collapsed_types:        0
% 7.58/1.50  num_pure_diseq_elim:                    0
% 7.58/1.50  simp_replaced_by:                       0
% 7.58/1.50  res_preprocessed:                       171
% 7.58/1.50  prep_upred:                             0
% 7.58/1.50  prep_unflattend:                        7
% 7.58/1.50  smt_new_axioms:                         0
% 7.58/1.50  pred_elim_cands:                        6
% 7.58/1.50  pred_elim:                              1
% 7.58/1.50  pred_elim_cl:                           2
% 7.58/1.50  pred_elim_cycles:                       3
% 7.58/1.50  merged_defs:                            0
% 7.58/1.50  merged_defs_ncl:                        0
% 7.58/1.50  bin_hyper_res:                          0
% 7.58/1.50  prep_cycles:                            4
% 7.58/1.50  pred_elim_time:                         0.002
% 7.58/1.50  splitting_time:                         0.
% 7.58/1.50  sem_filter_time:                        0.
% 7.58/1.50  monotx_time:                            0.
% 7.58/1.50  subtype_inf_time:                       0.
% 7.58/1.50  
% 7.58/1.50  ------ Problem properties
% 7.58/1.50  
% 7.58/1.50  clauses:                                33
% 7.58/1.50  conjectures:                            7
% 7.58/1.50  epr:                                    4
% 7.58/1.50  horn:                                   29
% 7.58/1.50  ground:                                 8
% 7.58/1.50  unary:                                  8
% 7.58/1.50  binary:                                 3
% 7.58/1.50  lits:                                   110
% 7.58/1.50  lits_eq:                                23
% 7.58/1.50  fd_pure:                                0
% 7.58/1.50  fd_pseudo:                              0
% 7.58/1.50  fd_cond:                                3
% 7.58/1.50  fd_pseudo_cond:                         0
% 7.58/1.50  ac_symbols:                             0
% 7.58/1.50  
% 7.58/1.50  ------ Propositional Solver
% 7.58/1.50  
% 7.58/1.50  prop_solver_calls:                      35
% 7.58/1.50  prop_fast_solver_calls:                 2748
% 7.58/1.50  smt_solver_calls:                       0
% 7.58/1.50  smt_fast_solver_calls:                  0
% 7.58/1.50  prop_num_of_clauses:                    8334
% 7.58/1.50  prop_preprocess_simplified:             13763
% 7.58/1.50  prop_fo_subsumed:                       286
% 7.58/1.50  prop_solver_time:                       0.
% 7.58/1.50  smt_solver_time:                        0.
% 7.58/1.50  smt_fast_solver_time:                   0.
% 7.58/1.50  prop_fast_solver_time:                  0.
% 7.58/1.50  prop_unsat_core_time:                   0.001
% 7.58/1.50  
% 7.58/1.50  ------ QBF
% 7.58/1.50  
% 7.58/1.50  qbf_q_res:                              0
% 7.58/1.50  qbf_num_tautologies:                    0
% 7.58/1.50  qbf_prep_cycles:                        0
% 7.58/1.50  
% 7.58/1.50  ------ BMC1
% 7.58/1.50  
% 7.58/1.50  bmc1_current_bound:                     -1
% 7.58/1.50  bmc1_last_solved_bound:                 -1
% 7.58/1.50  bmc1_unsat_core_size:                   -1
% 7.58/1.50  bmc1_unsat_core_parents_size:           -1
% 7.58/1.50  bmc1_merge_next_fun:                    0
% 7.58/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation
% 7.58/1.50  
% 7.58/1.50  inst_num_of_clauses:                    2651
% 7.58/1.50  inst_num_in_passive:                    397
% 7.58/1.50  inst_num_in_active:                     1063
% 7.58/1.50  inst_num_in_unprocessed:                1191
% 7.58/1.50  inst_num_of_loops:                      1260
% 7.58/1.50  inst_num_of_learning_restarts:          0
% 7.58/1.50  inst_num_moves_active_passive:          189
% 7.58/1.50  inst_lit_activity:                      0
% 7.58/1.50  inst_lit_activity_moves:                0
% 7.58/1.50  inst_num_tautologies:                   0
% 7.58/1.50  inst_num_prop_implied:                  0
% 7.58/1.50  inst_num_existing_simplified:           0
% 7.58/1.50  inst_num_eq_res_simplified:             0
% 7.58/1.50  inst_num_child_elim:                    0
% 7.58/1.50  inst_num_of_dismatching_blockings:      1150
% 7.58/1.50  inst_num_of_non_proper_insts:           2308
% 7.58/1.50  inst_num_of_duplicates:                 0
% 7.58/1.50  inst_inst_num_from_inst_to_res:         0
% 7.58/1.50  inst_dismatching_checking_time:         0.
% 7.58/1.50  
% 7.58/1.50  ------ Resolution
% 7.58/1.50  
% 7.58/1.50  res_num_of_clauses:                     0
% 7.58/1.50  res_num_in_passive:                     0
% 7.58/1.50  res_num_in_active:                      0
% 7.58/1.50  res_num_of_loops:                       175
% 7.58/1.50  res_forward_subset_subsumed:            147
% 7.58/1.50  res_backward_subset_subsumed:           0
% 7.58/1.50  res_forward_subsumed:                   0
% 7.58/1.50  res_backward_subsumed:                  0
% 7.58/1.50  res_forward_subsumption_resolution:     0
% 7.58/1.50  res_backward_subsumption_resolution:    0
% 7.58/1.50  res_clause_to_clause_subsumption:       2097
% 7.58/1.50  res_orphan_elimination:                 0
% 7.58/1.50  res_tautology_del:                      144
% 7.58/1.50  res_num_eq_res_simplified:              0
% 7.58/1.50  res_num_sel_changes:                    0
% 7.58/1.50  res_moves_from_active_to_pass:          0
% 7.58/1.50  
% 7.58/1.50  ------ Superposition
% 7.58/1.50  
% 7.58/1.50  sup_time_total:                         0.
% 7.58/1.50  sup_time_generating:                    0.
% 7.58/1.50  sup_time_sim_full:                      0.
% 7.58/1.50  sup_time_sim_immed:                     0.
% 7.58/1.50  
% 7.58/1.50  sup_num_of_clauses:                     288
% 7.58/1.50  sup_num_in_active:                      101
% 7.58/1.50  sup_num_in_passive:                     187
% 7.58/1.50  sup_num_of_loops:                       250
% 7.58/1.50  sup_fw_superposition:                   334
% 7.58/1.50  sup_bw_superposition:                   380
% 7.58/1.50  sup_immediate_simplified:               301
% 7.58/1.50  sup_given_eliminated:                   4
% 7.58/1.50  comparisons_done:                       0
% 7.58/1.50  comparisons_avoided:                    50
% 7.58/1.50  
% 7.58/1.50  ------ Simplifications
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  sim_fw_subset_subsumed:                 83
% 7.58/1.50  sim_bw_subset_subsumed:                 63
% 7.58/1.50  sim_fw_subsumed:                        61
% 7.58/1.50  sim_bw_subsumed:                        15
% 7.58/1.50  sim_fw_subsumption_res:                 0
% 7.58/1.50  sim_bw_subsumption_res:                 0
% 7.58/1.50  sim_tautology_del:                      2
% 7.58/1.50  sim_eq_tautology_del:                   151
% 7.58/1.50  sim_eq_res_simp:                        1
% 7.58/1.50  sim_fw_demodulated:                     7
% 7.58/1.50  sim_bw_demodulated:                     122
% 7.58/1.50  sim_light_normalised:                   215
% 7.58/1.50  sim_joinable_taut:                      0
% 7.58/1.50  sim_joinable_simp:                      0
% 7.58/1.50  sim_ac_normalised:                      0
% 7.58/1.50  sim_smt_subsumption:                    0
% 7.58/1.50  
%------------------------------------------------------------------------------
