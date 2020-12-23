%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:39 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :  389 (29214350 expanded)
%              Number of clauses        :  282 (7793654 expanded)
%              Number of leaves         :   31 (8206147 expanded)
%              Depth                    :   53
%              Number of atoms          : 1374 (179422850 expanded)
%              Number of equality atoms :  751 (33131685 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f63,plain,
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

fof(f66,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f59,f65,f64,f63])).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f109,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
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

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f115,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f112,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f60,plain,(
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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f92])).

fof(f116,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f119,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f94])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1586,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1582,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_37,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_48,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_536,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_48])).

cnf(c_537,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_49,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_541,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_49])).

cnf(c_542,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_1615,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1582,c_537,c_542])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1599,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2264,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1615,c_1599])).

cnf(c_44,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1614,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_44,c_537,c_542])).

cnf(c_2265,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2264,c_1614])).

cnf(c_2352,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2265,c_2264])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1592,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6779,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_1592])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_52,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_43,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_55,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2354,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2265,c_1615])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1581,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1613,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1581,c_537,c_542])).

cnf(c_2355,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2265,c_1613])).

cnf(c_7140,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6779,c_52,c_55,c_2354,c_2355])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1585,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1593,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5343,plain,
    ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X1,X0) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X0,X2),X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1593])).

cnf(c_9999,plain,
    ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_5343])).

cnf(c_10014,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7140,c_9999])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1755,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1756,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1611,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2677,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_1612])).

cnf(c_2829,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_2677])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1591,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6205,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_1591])).

cnf(c_11066,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10014,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1595,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11071,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11066,c_1595])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_656,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_27,c_23])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_660,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_14])).

cnf(c_1576,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_2615,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_1576])).

cnf(c_2359,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2355])).

cnf(c_2616,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2615])).

cnf(c_2830,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2829])).

cnf(c_2832,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2615,c_47,c_2359,c_2616,c_2830])).

cnf(c_2833,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2832])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1587,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5992,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_1587])).

cnf(c_7063,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5992,c_52,c_55,c_2354,c_2355])).

cnf(c_24,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_42,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_635,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_636,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_1577,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_1616,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1577,c_537,c_542])).

cnf(c_2353,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2265,c_1616])).

cnf(c_7067,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7063,c_2353])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1584,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7148,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7140,c_1584])).

cnf(c_7732,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7067,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,c_7148])).

cnf(c_7733,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7732])).

cnf(c_7736,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_7733])).

cnf(c_5,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1608,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1583,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1604,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4006,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1604])).

cnf(c_4358,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4006,c_52,c_2829])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1605,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6009,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4358,c_1605])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3227,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3228,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3227])).

cnf(c_6628,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6009,c_52,c_1756,c_2829,c_3228])).

cnf(c_6629,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6628])).

cnf(c_6635,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6629])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1602,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4126,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1602])).

cnf(c_4480,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_52,c_2829])).

cnf(c_6636,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6635,c_4480])).

cnf(c_6639,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6636,c_52,c_2829])).

cnf(c_6643,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_6639])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1603,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3369,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1603])).

cnf(c_3495,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_52,c_2829])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1589,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3497,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1589])).

cnf(c_3585,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3497,c_52,c_1756,c_2829,c_3228])).

cnf(c_3590,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3585,c_1599])).

cnf(c_4360,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4358,c_3590])).

cnf(c_5993,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4360,c_1587])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1600,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3089,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1600])).

cnf(c_1843,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1844,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_3375,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_52,c_55,c_1844,c_2829])).

cnf(c_5994,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5993,c_3375])).

cnf(c_4361,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4358,c_3585])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1588,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3498,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1588])).

cnf(c_3502,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3498,c_52,c_1756,c_2829,c_3228])).

cnf(c_4362,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4358,c_3502])).

cnf(c_6574,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5994,c_52,c_1756,c_2829,c_4361,c_4362])).

cnf(c_6575,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6574])).

cnf(c_6790,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_6643,c_6575])).

cnf(c_7737,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | sK2 != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7736,c_6790])).

cnf(c_7738,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7737])).

cnf(c_12844,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11071,c_7738])).

cnf(c_12848,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_12844])).

cnf(c_12874,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12848,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,c_6779])).

cnf(c_12896,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_7140])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1597,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5347,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1597])).

cnf(c_13411,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_5347])).

cnf(c_15063,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12896,c_13411])).

cnf(c_7134,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6205,c_52,c_55,c_2354,c_2355])).

cnf(c_12897,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_7134])).

cnf(c_26213,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15063,c_52,c_1756,c_2829,c_12897])).

cnf(c_12915,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_2354])).

cnf(c_13732,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12915,c_1597])).

cnf(c_12917,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_2355])).

cnf(c_14061,plain,
    ( sK2 = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13732,c_12917])).

cnf(c_14062,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_14061])).

cnf(c_7147,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_7140,c_1599])).

cnf(c_7150,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7147,c_4358])).

cnf(c_7372,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7150,c_1587])).

cnf(c_7373,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7372,c_3375])).

cnf(c_7728,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7373,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,c_6643,c_6779])).

cnf(c_12892,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_12874,c_7728])).

cnf(c_14063,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k1_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14062,c_12892])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_548,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_35])).

cnf(c_549,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_2123,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_2124,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),X0) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_2126,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2124])).

cnf(c_6780,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4360,c_1592])).

cnf(c_6781,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6780,c_3375])).

cnf(c_3460,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3461,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_6907,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6781,c_52,c_2829,c_3461])).

cnf(c_12900,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_6907])).

cnf(c_13655,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12900,c_1597])).

cnf(c_16524,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14063,c_52,c_55,c_1756,c_2126,c_2354,c_2355,c_2829,c_6205,c_6779,c_12848,c_13655])).

cnf(c_12891,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_7733])).

cnf(c_16532,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16524,c_12891])).

cnf(c_23247,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16524,c_16532])).

cnf(c_23333,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23247,c_12915])).

cnf(c_23334,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23333])).

cnf(c_23338,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16524,c_23334])).

cnf(c_23337,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_23334])).

cnf(c_23345,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23338,c_52,c_1756,c_2829,c_12896,c_12897,c_23337])).

cnf(c_26215,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26213,c_23345])).

cnf(c_5342,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_tops_2(X1,X2,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1612])).

cnf(c_9062,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7140,c_5342])).

cnf(c_9822,plain,
    ( v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9062,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205])).

cnf(c_12883,plain,
    ( v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12874,c_9822])).

cnf(c_7982,plain,
    ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7148,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205])).

cnf(c_1610,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3016,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1599])).

cnf(c_3817,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1610,c_3016])).

cnf(c_162,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7379,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3817,c_162])).

cnf(c_7380,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7379])).

cnf(c_7988,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))))
    | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7982,c_7380])).

cnf(c_15172,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))))
    | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7988,c_12874])).

cnf(c_19415,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))))
    | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12883,c_15172])).

cnf(c_30017,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))))
    | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19415,c_23345])).

cnf(c_30019,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_1611,c_30017])).

cnf(c_30277,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))))
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26215,c_30019])).

cnf(c_12909,plain,
    ( k2_relset_1(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_12874,c_4360])).

cnf(c_23395,plain,
    ( k2_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23345,c_12909])).

cnf(c_12913,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12874,c_3495])).

cnf(c_23404,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23345,c_12913])).

cnf(c_23410,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23345,c_4358])).

cnf(c_30284,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_30277,c_23395,c_23404,c_23410])).

cnf(c_976,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1013,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_977,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1745,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1746,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_983,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3191,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | X0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_3909,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(X0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3191])).

cnf(c_3910,plain,
    ( k2_funct_1(X0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3909])).

cnf(c_3912,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3910])).

cnf(c_982,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_7156,plain,
    ( X0 != sK2
    | k2_funct_1(X0) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_7157,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_7156])).

cnf(c_23379,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23345,c_12896])).

cnf(c_23382,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23345,c_12897])).

cnf(c_23378,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23345,c_12891])).

cnf(c_26225,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26215,c_23378])).

cnf(c_29911,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_26225])).

cnf(c_23394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23345,c_12915])).

cnf(c_29912,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26215,c_26225])).

cnf(c_30864,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29911,c_23394,c_29912])).

cnf(c_30865,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_30864])).

cnf(c_30868,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_30865])).

cnf(c_31248,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30284,c_52,c_1013,c_1746,c_1756,c_2829,c_3912,c_7157,c_12896,c_12897,c_23337,c_23379,c_23382,c_30868])).

cnf(c_31268,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31248,c_23378])).

cnf(c_53,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_134,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_136,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_687,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | X0 != X2
    | k1_relat_1(X2) = X3
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_688,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_689,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_691,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1726,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_1727,plain,
    ( X0 != sK2
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_1729,plain,
    ( k1_xboole_0 != sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2911,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_2912,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_978,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3159,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_3174,plain,
    ( X0 != sK2
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3159])).

cnf(c_3176,plain,
    ( k1_xboole_0 != sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3174])).

cnf(c_2561,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_3398,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_4110,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_7580,plain,
    ( X0 = u1_struct_0(sK0)
    | X0 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4110])).

cnf(c_7581,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7580])).

cnf(c_4145,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_8117,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4145])).

cnf(c_8118,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8117])).

cnf(c_11508,plain,
    ( ~ v1_funct_2(k2_funct_1(X0),X1,X2)
    | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k2_funct_1(X0)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_11509,plain,
    ( v1_funct_2(k2_funct_1(X0),X1,X2) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11508])).

cnf(c_11511,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11509])).

cnf(c_990,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_11528,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X2 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_11529,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X2 != sK2
    | v1_funct_2(X2,X1,X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11528])).

cnf(c_11531,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != sK2
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11529])).

cnf(c_12204,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_12205,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12204])).

cnf(c_2356,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2265,c_537])).

cnf(c_12918,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12874,c_2356])).

cnf(c_11571,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | X1 != u1_struct_0(sK1)
    | X2 != u1_struct_0(sK0)
    | X0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_24877,plain,
    ( v1_funct_2(k2_funct_1(X0),X1,X2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | X1 != u1_struct_0(sK1)
    | X2 != u1_struct_0(sK0)
    | k2_funct_1(X0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11571])).

cnf(c_24878,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | k2_funct_1(X2) != k2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(X2),X0,X1) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24877])).

cnf(c_24880,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24878])).

cnf(c_31269,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31248,c_23379])).

cnf(c_23391,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23345,c_12892])).

cnf(c_31272,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31248,c_23391])).

cnf(c_31275,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31248,c_23394])).

cnf(c_34171,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31268,c_52,c_53,c_54,c_44,c_55,c_136,c_537,c_542,c_691,c_1013,c_1729,c_1746,c_1756,c_2829,c_2912,c_3176,c_3398,c_3912,c_7157,c_7581,c_8118,c_11511,c_11531,c_12205,c_12896,c_12897,c_12918,c_23337,c_23379,c_23382,c_24880,c_30868,c_31269,c_31272,c_31275])).

cnf(c_33793,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31272,c_52,c_53,c_136,c_542,c_691,c_1013,c_1729,c_1746,c_1756,c_2829,c_2912,c_3176,c_3912,c_7157,c_7581,c_11531,c_12205,c_12896,c_12897,c_12918,c_23337,c_23379,c_23382,c_30868,c_31275])).

cnf(c_34175,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34171,c_33793])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34175,c_30868,c_23382,c_23379,c_23337,c_12918,c_12897,c_12896,c_12205,c_11531,c_7581,c_7157,c_3912,c_2912,c_2829,c_1756,c_1746,c_1013,c_542,c_53,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.59/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.59/2.00  
% 11.59/2.00  ------  iProver source info
% 11.59/2.00  
% 11.59/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.59/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.59/2.00  git: non_committed_changes: false
% 11.59/2.00  git: last_make_outside_of_git: false
% 11.59/2.00  
% 11.59/2.00  ------ 
% 11.59/2.00  
% 11.59/2.00  ------ Input Options
% 11.59/2.00  
% 11.59/2.00  --out_options                           all
% 11.59/2.00  --tptp_safe_out                         true
% 11.59/2.00  --problem_path                          ""
% 11.59/2.00  --include_path                          ""
% 11.59/2.00  --clausifier                            res/vclausify_rel
% 11.59/2.00  --clausifier_options                    ""
% 11.59/2.00  --stdin                                 false
% 11.59/2.00  --stats_out                             all
% 11.59/2.00  
% 11.59/2.00  ------ General Options
% 11.59/2.00  
% 11.59/2.00  --fof                                   false
% 11.59/2.00  --time_out_real                         305.
% 11.59/2.00  --time_out_virtual                      -1.
% 11.59/2.00  --symbol_type_check                     false
% 11.59/2.00  --clausify_out                          false
% 11.59/2.00  --sig_cnt_out                           false
% 11.59/2.00  --trig_cnt_out                          false
% 11.59/2.00  --trig_cnt_out_tolerance                1.
% 11.59/2.00  --trig_cnt_out_sk_spl                   false
% 11.59/2.00  --abstr_cl_out                          false
% 11.59/2.00  
% 11.59/2.00  ------ Global Options
% 11.59/2.00  
% 11.59/2.00  --schedule                              default
% 11.59/2.00  --add_important_lit                     false
% 11.59/2.00  --prop_solver_per_cl                    1000
% 11.59/2.00  --min_unsat_core                        false
% 11.59/2.00  --soft_assumptions                      false
% 11.59/2.00  --soft_lemma_size                       3
% 11.59/2.00  --prop_impl_unit_size                   0
% 11.59/2.00  --prop_impl_unit                        []
% 11.59/2.00  --share_sel_clauses                     true
% 11.59/2.00  --reset_solvers                         false
% 11.59/2.00  --bc_imp_inh                            [conj_cone]
% 11.59/2.00  --conj_cone_tolerance                   3.
% 11.59/2.00  --extra_neg_conj                        none
% 11.59/2.00  --large_theory_mode                     true
% 11.59/2.00  --prolific_symb_bound                   200
% 11.59/2.00  --lt_threshold                          2000
% 11.59/2.00  --clause_weak_htbl                      true
% 11.59/2.00  --gc_record_bc_elim                     false
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing Options
% 11.59/2.00  
% 11.59/2.00  --preprocessing_flag                    true
% 11.59/2.00  --time_out_prep_mult                    0.1
% 11.59/2.00  --splitting_mode                        input
% 11.59/2.00  --splitting_grd                         true
% 11.59/2.00  --splitting_cvd                         false
% 11.59/2.00  --splitting_cvd_svl                     false
% 11.59/2.00  --splitting_nvd                         32
% 11.59/2.00  --sub_typing                            true
% 11.59/2.00  --prep_gs_sim                           true
% 11.59/2.00  --prep_unflatten                        true
% 11.59/2.00  --prep_res_sim                          true
% 11.59/2.00  --prep_upred                            true
% 11.59/2.00  --prep_sem_filter                       exhaustive
% 11.59/2.00  --prep_sem_filter_out                   false
% 11.59/2.00  --pred_elim                             true
% 11.59/2.00  --res_sim_input                         true
% 11.59/2.00  --eq_ax_congr_red                       true
% 11.59/2.00  --pure_diseq_elim                       true
% 11.59/2.00  --brand_transform                       false
% 11.59/2.00  --non_eq_to_eq                          false
% 11.59/2.00  --prep_def_merge                        true
% 11.59/2.00  --prep_def_merge_prop_impl              false
% 11.59/2.00  --prep_def_merge_mbd                    true
% 11.59/2.00  --prep_def_merge_tr_red                 false
% 11.59/2.00  --prep_def_merge_tr_cl                  false
% 11.59/2.00  --smt_preprocessing                     true
% 11.59/2.00  --smt_ac_axioms                         fast
% 11.59/2.00  --preprocessed_out                      false
% 11.59/2.00  --preprocessed_stats                    false
% 11.59/2.00  
% 11.59/2.00  ------ Abstraction refinement Options
% 11.59/2.00  
% 11.59/2.00  --abstr_ref                             []
% 11.59/2.00  --abstr_ref_prep                        false
% 11.59/2.00  --abstr_ref_until_sat                   false
% 11.59/2.00  --abstr_ref_sig_restrict                funpre
% 11.59/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/2.00  --abstr_ref_under                       []
% 11.59/2.00  
% 11.59/2.00  ------ SAT Options
% 11.59/2.00  
% 11.59/2.00  --sat_mode                              false
% 11.59/2.00  --sat_fm_restart_options                ""
% 11.59/2.00  --sat_gr_def                            false
% 11.59/2.00  --sat_epr_types                         true
% 11.59/2.00  --sat_non_cyclic_types                  false
% 11.59/2.00  --sat_finite_models                     false
% 11.59/2.00  --sat_fm_lemmas                         false
% 11.59/2.00  --sat_fm_prep                           false
% 11.59/2.00  --sat_fm_uc_incr                        true
% 11.59/2.00  --sat_out_model                         small
% 11.59/2.00  --sat_out_clauses                       false
% 11.59/2.00  
% 11.59/2.00  ------ QBF Options
% 11.59/2.00  
% 11.59/2.00  --qbf_mode                              false
% 11.59/2.00  --qbf_elim_univ                         false
% 11.59/2.00  --qbf_dom_inst                          none
% 11.59/2.00  --qbf_dom_pre_inst                      false
% 11.59/2.00  --qbf_sk_in                             false
% 11.59/2.00  --qbf_pred_elim                         true
% 11.59/2.00  --qbf_split                             512
% 11.59/2.00  
% 11.59/2.00  ------ BMC1 Options
% 11.59/2.00  
% 11.59/2.00  --bmc1_incremental                      false
% 11.59/2.00  --bmc1_axioms                           reachable_all
% 11.59/2.00  --bmc1_min_bound                        0
% 11.59/2.00  --bmc1_max_bound                        -1
% 11.59/2.00  --bmc1_max_bound_default                -1
% 11.59/2.00  --bmc1_symbol_reachability              true
% 11.59/2.00  --bmc1_property_lemmas                  false
% 11.59/2.00  --bmc1_k_induction                      false
% 11.59/2.00  --bmc1_non_equiv_states                 false
% 11.59/2.00  --bmc1_deadlock                         false
% 11.59/2.00  --bmc1_ucm                              false
% 11.59/2.00  --bmc1_add_unsat_core                   none
% 11.59/2.00  --bmc1_unsat_core_children              false
% 11.59/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/2.00  --bmc1_out_stat                         full
% 11.59/2.00  --bmc1_ground_init                      false
% 11.59/2.00  --bmc1_pre_inst_next_state              false
% 11.59/2.00  --bmc1_pre_inst_state                   false
% 11.59/2.00  --bmc1_pre_inst_reach_state             false
% 11.59/2.00  --bmc1_out_unsat_core                   false
% 11.59/2.00  --bmc1_aig_witness_out                  false
% 11.59/2.00  --bmc1_verbose                          false
% 11.59/2.00  --bmc1_dump_clauses_tptp                false
% 11.59/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.59/2.00  --bmc1_dump_file                        -
% 11.59/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.59/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.59/2.00  --bmc1_ucm_extend_mode                  1
% 11.59/2.00  --bmc1_ucm_init_mode                    2
% 11.59/2.00  --bmc1_ucm_cone_mode                    none
% 11.59/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.59/2.00  --bmc1_ucm_relax_model                  4
% 11.59/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.59/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/2.00  --bmc1_ucm_layered_model                none
% 11.59/2.00  --bmc1_ucm_max_lemma_size               10
% 11.59/2.00  
% 11.59/2.00  ------ AIG Options
% 11.59/2.00  
% 11.59/2.00  --aig_mode                              false
% 11.59/2.00  
% 11.59/2.00  ------ Instantiation Options
% 11.59/2.00  
% 11.59/2.00  --instantiation_flag                    true
% 11.59/2.00  --inst_sos_flag                         true
% 11.59/2.00  --inst_sos_phase                        true
% 11.59/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/2.00  --inst_lit_sel_side                     num_symb
% 11.59/2.00  --inst_solver_per_active                1400
% 11.59/2.00  --inst_solver_calls_frac                1.
% 11.59/2.00  --inst_passive_queue_type               priority_queues
% 11.59/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/2.00  --inst_passive_queues_freq              [25;2]
% 11.59/2.00  --inst_dismatching                      true
% 11.59/2.00  --inst_eager_unprocessed_to_passive     true
% 11.59/2.00  --inst_prop_sim_given                   true
% 11.59/2.00  --inst_prop_sim_new                     false
% 11.59/2.00  --inst_subs_new                         false
% 11.59/2.00  --inst_eq_res_simp                      false
% 11.59/2.00  --inst_subs_given                       false
% 11.59/2.00  --inst_orphan_elimination               true
% 11.59/2.00  --inst_learning_loop_flag               true
% 11.59/2.00  --inst_learning_start                   3000
% 11.59/2.00  --inst_learning_factor                  2
% 11.59/2.00  --inst_start_prop_sim_after_learn       3
% 11.59/2.00  --inst_sel_renew                        solver
% 11.59/2.00  --inst_lit_activity_flag                true
% 11.59/2.00  --inst_restr_to_given                   false
% 11.59/2.00  --inst_activity_threshold               500
% 11.59/2.00  --inst_out_proof                        true
% 11.59/2.00  
% 11.59/2.00  ------ Resolution Options
% 11.59/2.00  
% 11.59/2.00  --resolution_flag                       true
% 11.59/2.00  --res_lit_sel                           adaptive
% 11.59/2.00  --res_lit_sel_side                      none
% 11.59/2.00  --res_ordering                          kbo
% 11.59/2.00  --res_to_prop_solver                    active
% 11.59/2.00  --res_prop_simpl_new                    false
% 11.59/2.00  --res_prop_simpl_given                  true
% 11.59/2.00  --res_passive_queue_type                priority_queues
% 11.59/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/2.00  --res_passive_queues_freq               [15;5]
% 11.59/2.00  --res_forward_subs                      full
% 11.59/2.00  --res_backward_subs                     full
% 11.59/2.00  --res_forward_subs_resolution           true
% 11.59/2.00  --res_backward_subs_resolution          true
% 11.59/2.00  --res_orphan_elimination                true
% 11.59/2.00  --res_time_limit                        2.
% 11.59/2.00  --res_out_proof                         true
% 11.59/2.00  
% 11.59/2.00  ------ Superposition Options
% 11.59/2.00  
% 11.59/2.00  --superposition_flag                    true
% 11.59/2.00  --sup_passive_queue_type                priority_queues
% 11.59/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.59/2.00  --demod_completeness_check              fast
% 11.59/2.00  --demod_use_ground                      true
% 11.59/2.00  --sup_to_prop_solver                    passive
% 11.59/2.00  --sup_prop_simpl_new                    true
% 11.59/2.00  --sup_prop_simpl_given                  true
% 11.59/2.00  --sup_fun_splitting                     true
% 11.59/2.00  --sup_smt_interval                      50000
% 11.59/2.00  
% 11.59/2.00  ------ Superposition Simplification Setup
% 11.59/2.00  
% 11.59/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.59/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.59/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.59/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.59/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.59/2.00  --sup_immed_triv                        [TrivRules]
% 11.59/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_immed_bw_main                     []
% 11.59/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.59/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_input_bw                          []
% 11.59/2.00  
% 11.59/2.00  ------ Combination Options
% 11.59/2.00  
% 11.59/2.00  --comb_res_mult                         3
% 11.59/2.00  --comb_sup_mult                         2
% 11.59/2.00  --comb_inst_mult                        10
% 11.59/2.00  
% 11.59/2.00  ------ Debug Options
% 11.59/2.00  
% 11.59/2.00  --dbg_backtrace                         false
% 11.59/2.00  --dbg_dump_prop_clauses                 false
% 11.59/2.00  --dbg_dump_prop_clauses_file            -
% 11.59/2.00  --dbg_out_stat                          false
% 11.59/2.00  ------ Parsing...
% 11.59/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.59/2.00  ------ Proving...
% 11.59/2.00  ------ Problem Properties 
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  clauses                                 41
% 11.59/2.00  conjectures                             5
% 11.59/2.00  EPR                                     2
% 11.59/2.00  Horn                                    36
% 11.59/2.00  unary                                   10
% 11.59/2.00  binary                                  1
% 11.59/2.00  lits                                    141
% 11.59/2.00  lits eq                                 31
% 11.59/2.00  fd_pure                                 0
% 11.59/2.00  fd_pseudo                               0
% 11.59/2.00  fd_cond                                 3
% 11.59/2.00  fd_pseudo_cond                          1
% 11.59/2.00  AC symbols                              0
% 11.59/2.00  
% 11.59/2.00  ------ Schedule dynamic 5 is on 
% 11.59/2.00  
% 11.59/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  ------ 
% 11.59/2.00  Current options:
% 11.59/2.00  ------ 
% 11.59/2.00  
% 11.59/2.00  ------ Input Options
% 11.59/2.00  
% 11.59/2.00  --out_options                           all
% 11.59/2.00  --tptp_safe_out                         true
% 11.59/2.00  --problem_path                          ""
% 11.59/2.00  --include_path                          ""
% 11.59/2.00  --clausifier                            res/vclausify_rel
% 11.59/2.00  --clausifier_options                    ""
% 11.59/2.00  --stdin                                 false
% 11.59/2.00  --stats_out                             all
% 11.59/2.00  
% 11.59/2.00  ------ General Options
% 11.59/2.00  
% 11.59/2.00  --fof                                   false
% 11.59/2.00  --time_out_real                         305.
% 11.59/2.00  --time_out_virtual                      -1.
% 11.59/2.00  --symbol_type_check                     false
% 11.59/2.00  --clausify_out                          false
% 11.59/2.00  --sig_cnt_out                           false
% 11.59/2.00  --trig_cnt_out                          false
% 11.59/2.00  --trig_cnt_out_tolerance                1.
% 11.59/2.00  --trig_cnt_out_sk_spl                   false
% 11.59/2.00  --abstr_cl_out                          false
% 11.59/2.00  
% 11.59/2.00  ------ Global Options
% 11.59/2.00  
% 11.59/2.00  --schedule                              default
% 11.59/2.00  --add_important_lit                     false
% 11.59/2.00  --prop_solver_per_cl                    1000
% 11.59/2.00  --min_unsat_core                        false
% 11.59/2.00  --soft_assumptions                      false
% 11.59/2.00  --soft_lemma_size                       3
% 11.59/2.00  --prop_impl_unit_size                   0
% 11.59/2.00  --prop_impl_unit                        []
% 11.59/2.00  --share_sel_clauses                     true
% 11.59/2.00  --reset_solvers                         false
% 11.59/2.00  --bc_imp_inh                            [conj_cone]
% 11.59/2.00  --conj_cone_tolerance                   3.
% 11.59/2.00  --extra_neg_conj                        none
% 11.59/2.00  --large_theory_mode                     true
% 11.59/2.00  --prolific_symb_bound                   200
% 11.59/2.00  --lt_threshold                          2000
% 11.59/2.00  --clause_weak_htbl                      true
% 11.59/2.00  --gc_record_bc_elim                     false
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing Options
% 11.59/2.00  
% 11.59/2.00  --preprocessing_flag                    true
% 11.59/2.00  --time_out_prep_mult                    0.1
% 11.59/2.00  --splitting_mode                        input
% 11.59/2.00  --splitting_grd                         true
% 11.59/2.00  --splitting_cvd                         false
% 11.59/2.00  --splitting_cvd_svl                     false
% 11.59/2.00  --splitting_nvd                         32
% 11.59/2.00  --sub_typing                            true
% 11.59/2.00  --prep_gs_sim                           true
% 11.59/2.00  --prep_unflatten                        true
% 11.59/2.00  --prep_res_sim                          true
% 11.59/2.00  --prep_upred                            true
% 11.59/2.00  --prep_sem_filter                       exhaustive
% 11.59/2.00  --prep_sem_filter_out                   false
% 11.59/2.00  --pred_elim                             true
% 11.59/2.00  --res_sim_input                         true
% 11.59/2.00  --eq_ax_congr_red                       true
% 11.59/2.00  --pure_diseq_elim                       true
% 11.59/2.00  --brand_transform                       false
% 11.59/2.00  --non_eq_to_eq                          false
% 11.59/2.00  --prep_def_merge                        true
% 11.59/2.00  --prep_def_merge_prop_impl              false
% 11.59/2.00  --prep_def_merge_mbd                    true
% 11.59/2.00  --prep_def_merge_tr_red                 false
% 11.59/2.00  --prep_def_merge_tr_cl                  false
% 11.59/2.00  --smt_preprocessing                     true
% 11.59/2.00  --smt_ac_axioms                         fast
% 11.59/2.00  --preprocessed_out                      false
% 11.59/2.00  --preprocessed_stats                    false
% 11.59/2.00  
% 11.59/2.00  ------ Abstraction refinement Options
% 11.59/2.00  
% 11.59/2.00  --abstr_ref                             []
% 11.59/2.00  --abstr_ref_prep                        false
% 11.59/2.00  --abstr_ref_until_sat                   false
% 11.59/2.00  --abstr_ref_sig_restrict                funpre
% 11.59/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/2.00  --abstr_ref_under                       []
% 11.59/2.00  
% 11.59/2.00  ------ SAT Options
% 11.59/2.00  
% 11.59/2.00  --sat_mode                              false
% 11.59/2.00  --sat_fm_restart_options                ""
% 11.59/2.00  --sat_gr_def                            false
% 11.59/2.00  --sat_epr_types                         true
% 11.59/2.00  --sat_non_cyclic_types                  false
% 11.59/2.00  --sat_finite_models                     false
% 11.59/2.00  --sat_fm_lemmas                         false
% 11.59/2.00  --sat_fm_prep                           false
% 11.59/2.00  --sat_fm_uc_incr                        true
% 11.59/2.00  --sat_out_model                         small
% 11.59/2.00  --sat_out_clauses                       false
% 11.59/2.00  
% 11.59/2.00  ------ QBF Options
% 11.59/2.00  
% 11.59/2.00  --qbf_mode                              false
% 11.59/2.00  --qbf_elim_univ                         false
% 11.59/2.00  --qbf_dom_inst                          none
% 11.59/2.00  --qbf_dom_pre_inst                      false
% 11.59/2.00  --qbf_sk_in                             false
% 11.59/2.00  --qbf_pred_elim                         true
% 11.59/2.00  --qbf_split                             512
% 11.59/2.00  
% 11.59/2.00  ------ BMC1 Options
% 11.59/2.00  
% 11.59/2.00  --bmc1_incremental                      false
% 11.59/2.00  --bmc1_axioms                           reachable_all
% 11.59/2.00  --bmc1_min_bound                        0
% 11.59/2.00  --bmc1_max_bound                        -1
% 11.59/2.00  --bmc1_max_bound_default                -1
% 11.59/2.00  --bmc1_symbol_reachability              true
% 11.59/2.00  --bmc1_property_lemmas                  false
% 11.59/2.00  --bmc1_k_induction                      false
% 11.59/2.00  --bmc1_non_equiv_states                 false
% 11.59/2.00  --bmc1_deadlock                         false
% 11.59/2.00  --bmc1_ucm                              false
% 11.59/2.00  --bmc1_add_unsat_core                   none
% 11.59/2.00  --bmc1_unsat_core_children              false
% 11.59/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/2.00  --bmc1_out_stat                         full
% 11.59/2.00  --bmc1_ground_init                      false
% 11.59/2.00  --bmc1_pre_inst_next_state              false
% 11.59/2.00  --bmc1_pre_inst_state                   false
% 11.59/2.00  --bmc1_pre_inst_reach_state             false
% 11.59/2.00  --bmc1_out_unsat_core                   false
% 11.59/2.00  --bmc1_aig_witness_out                  false
% 11.59/2.00  --bmc1_verbose                          false
% 11.59/2.00  --bmc1_dump_clauses_tptp                false
% 11.59/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.59/2.00  --bmc1_dump_file                        -
% 11.59/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.59/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.59/2.00  --bmc1_ucm_extend_mode                  1
% 11.59/2.00  --bmc1_ucm_init_mode                    2
% 11.59/2.00  --bmc1_ucm_cone_mode                    none
% 11.59/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.59/2.00  --bmc1_ucm_relax_model                  4
% 11.59/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.59/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/2.00  --bmc1_ucm_layered_model                none
% 11.59/2.00  --bmc1_ucm_max_lemma_size               10
% 11.59/2.00  
% 11.59/2.00  ------ AIG Options
% 11.59/2.00  
% 11.59/2.00  --aig_mode                              false
% 11.59/2.00  
% 11.59/2.00  ------ Instantiation Options
% 11.59/2.00  
% 11.59/2.00  --instantiation_flag                    true
% 11.59/2.00  --inst_sos_flag                         true
% 11.59/2.00  --inst_sos_phase                        true
% 11.59/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/2.00  --inst_lit_sel_side                     none
% 11.59/2.00  --inst_solver_per_active                1400
% 11.59/2.00  --inst_solver_calls_frac                1.
% 11.59/2.00  --inst_passive_queue_type               priority_queues
% 11.59/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/2.00  --inst_passive_queues_freq              [25;2]
% 11.59/2.00  --inst_dismatching                      true
% 11.59/2.00  --inst_eager_unprocessed_to_passive     true
% 11.59/2.00  --inst_prop_sim_given                   true
% 11.59/2.00  --inst_prop_sim_new                     false
% 11.59/2.00  --inst_subs_new                         false
% 11.59/2.00  --inst_eq_res_simp                      false
% 11.59/2.00  --inst_subs_given                       false
% 11.59/2.00  --inst_orphan_elimination               true
% 11.59/2.00  --inst_learning_loop_flag               true
% 11.59/2.00  --inst_learning_start                   3000
% 11.59/2.00  --inst_learning_factor                  2
% 11.59/2.00  --inst_start_prop_sim_after_learn       3
% 11.59/2.00  --inst_sel_renew                        solver
% 11.59/2.00  --inst_lit_activity_flag                true
% 11.59/2.00  --inst_restr_to_given                   false
% 11.59/2.00  --inst_activity_threshold               500
% 11.59/2.00  --inst_out_proof                        true
% 11.59/2.00  
% 11.59/2.00  ------ Resolution Options
% 11.59/2.00  
% 11.59/2.00  --resolution_flag                       false
% 11.59/2.00  --res_lit_sel                           adaptive
% 11.59/2.00  --res_lit_sel_side                      none
% 11.59/2.00  --res_ordering                          kbo
% 11.59/2.00  --res_to_prop_solver                    active
% 11.59/2.00  --res_prop_simpl_new                    false
% 11.59/2.00  --res_prop_simpl_given                  true
% 11.59/2.00  --res_passive_queue_type                priority_queues
% 11.59/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/2.00  --res_passive_queues_freq               [15;5]
% 11.59/2.00  --res_forward_subs                      full
% 11.59/2.00  --res_backward_subs                     full
% 11.59/2.00  --res_forward_subs_resolution           true
% 11.59/2.00  --res_backward_subs_resolution          true
% 11.59/2.00  --res_orphan_elimination                true
% 11.59/2.00  --res_time_limit                        2.
% 11.59/2.00  --res_out_proof                         true
% 11.59/2.00  
% 11.59/2.00  ------ Superposition Options
% 11.59/2.00  
% 11.59/2.00  --superposition_flag                    true
% 11.59/2.00  --sup_passive_queue_type                priority_queues
% 11.59/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.59/2.00  --demod_completeness_check              fast
% 11.59/2.00  --demod_use_ground                      true
% 11.59/2.00  --sup_to_prop_solver                    passive
% 11.59/2.00  --sup_prop_simpl_new                    true
% 11.59/2.00  --sup_prop_simpl_given                  true
% 11.59/2.00  --sup_fun_splitting                     true
% 11.59/2.00  --sup_smt_interval                      50000
% 11.59/2.00  
% 11.59/2.00  ------ Superposition Simplification Setup
% 11.59/2.00  
% 11.59/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.59/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.59/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.59/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.59/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.59/2.00  --sup_immed_triv                        [TrivRules]
% 11.59/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_immed_bw_main                     []
% 11.59/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.59/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.00  --sup_input_bw                          []
% 11.59/2.00  
% 11.59/2.00  ------ Combination Options
% 11.59/2.00  
% 11.59/2.00  --comb_res_mult                         3
% 11.59/2.00  --comb_sup_mult                         2
% 11.59/2.00  --comb_inst_mult                        10
% 11.59/2.00  
% 11.59/2.00  ------ Debug Options
% 11.59/2.00  
% 11.59/2.00  --dbg_backtrace                         false
% 11.59/2.00  --dbg_dump_prop_clauses                 false
% 11.59/2.00  --dbg_dump_prop_clauses_file            -
% 11.59/2.00  --dbg_out_stat                          false
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  ------ Proving...
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  % SZS status Theorem for theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  fof(f21,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f56,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.59/2.00    inference(ennf_transformation,[],[f21])).
% 11.59/2.00  
% 11.59/2.00  fof(f57,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(flattening,[],[f56])).
% 11.59/2.00  
% 11.59/2.00  fof(f108,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f57])).
% 11.59/2.00  
% 11.59/2.00  fof(f22,conjecture,(
% 11.59/2.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f23,negated_conjecture,(
% 11.59/2.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.59/2.00    inference(negated_conjecture,[],[f22])).
% 11.59/2.00  
% 11.59/2.00  fof(f24,plain,(
% 11.59/2.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.59/2.00    inference(pure_predicate_removal,[],[f23])).
% 11.59/2.00  
% 11.59/2.00  fof(f58,plain,(
% 11.59/2.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 11.59/2.00    inference(ennf_transformation,[],[f24])).
% 11.59/2.00  
% 11.59/2.00  fof(f59,plain,(
% 11.59/2.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 11.59/2.00    inference(flattening,[],[f58])).
% 11.59/2.00  
% 11.59/2.00  fof(f65,plain,(
% 11.59/2.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f64,plain,(
% 11.59/2.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f63,plain,(
% 11.59/2.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f66,plain,(
% 11.59/2.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 11.59/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f59,f65,f64,f63])).
% 11.59/2.00  
% 11.59/2.00  fof(f113,plain,(
% 11.59/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f19,axiom,(
% 11.59/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f53,plain,(
% 11.59/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.59/2.00    inference(ennf_transformation,[],[f19])).
% 11.59/2.00  
% 11.59/2.00  fof(f104,plain,(
% 11.59/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f53])).
% 11.59/2.00  
% 11.59/2.00  fof(f110,plain,(
% 11.59/2.00    l1_struct_0(sK1)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f109,plain,(
% 11.59/2.00    l1_struct_0(sK0)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f11,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f38,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.59/2.00    inference(ennf_transformation,[],[f11])).
% 11.59/2.00  
% 11.59/2.00  fof(f82,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f38])).
% 11.59/2.00  
% 11.59/2.00  fof(f114,plain,(
% 11.59/2.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f16,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f47,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.59/2.00    inference(ennf_transformation,[],[f16])).
% 11.59/2.00  
% 11.59/2.00  fof(f48,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(flattening,[],[f47])).
% 11.59/2.00  
% 11.59/2.00  fof(f97,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f48])).
% 11.59/2.00  
% 11.59/2.00  fof(f111,plain,(
% 11.59/2.00    v1_funct_1(sK2)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f115,plain,(
% 11.59/2.00    v2_funct_1(sK2)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f112,plain,(
% 11.59/2.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f107,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f57])).
% 11.59/2.00  
% 11.59/2.00  fof(f12,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f39,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.59/2.00    inference(ennf_transformation,[],[f12])).
% 11.59/2.00  
% 11.59/2.00  fof(f40,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.59/2.00    inference(flattening,[],[f39])).
% 11.59/2.00  
% 11.59/2.00  fof(f60,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.59/2.00    inference(nnf_transformation,[],[f40])).
% 11.59/2.00  
% 11.59/2.00  fof(f83,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f60])).
% 11.59/2.00  
% 11.59/2.00  fof(f4,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f27,plain,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f4])).
% 11.59/2.00  
% 11.59/2.00  fof(f28,plain,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f27])).
% 11.59/2.00  
% 11.59/2.00  fof(f71,plain,(
% 11.59/2.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f28])).
% 11.59/2.00  
% 11.59/2.00  fof(f3,axiom,(
% 11.59/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f69,plain,(
% 11.59/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f3])).
% 11.59/2.00  
% 11.59/2.00  fof(f2,axiom,(
% 11.59/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f26,plain,(
% 11.59/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(ennf_transformation,[],[f2])).
% 11.59/2.00  
% 11.59/2.00  fof(f68,plain,(
% 11.59/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f26])).
% 11.59/2.00  
% 11.59/2.00  fof(f96,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f48])).
% 11.59/2.00  
% 11.59/2.00  fof(f85,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f60])).
% 11.59/2.00  
% 11.59/2.00  fof(f15,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f45,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.59/2.00    inference(ennf_transformation,[],[f15])).
% 11.59/2.00  
% 11.59/2.00  fof(f46,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(flattening,[],[f45])).
% 11.59/2.00  
% 11.59/2.00  fof(f93,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f46])).
% 11.59/2.00  
% 11.59/2.00  fof(f13,axiom,(
% 11.59/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f41,plain,(
% 11.59/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.59/2.00    inference(ennf_transformation,[],[f13])).
% 11.59/2.00  
% 11.59/2.00  fof(f42,plain,(
% 11.59/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.59/2.00    inference(flattening,[],[f41])).
% 11.59/2.00  
% 11.59/2.00  fof(f61,plain,(
% 11.59/2.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.59/2.00    inference(nnf_transformation,[],[f42])).
% 11.59/2.00  
% 11.59/2.00  fof(f89,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f61])).
% 11.59/2.00  
% 11.59/2.00  fof(f10,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f25,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.59/2.00    inference(pure_predicate_removal,[],[f10])).
% 11.59/2.00  
% 11.59/2.00  fof(f37,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.59/2.00    inference(ennf_transformation,[],[f25])).
% 11.59/2.00  
% 11.59/2.00  fof(f81,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f37])).
% 11.59/2.00  
% 11.59/2.00  fof(f20,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f54,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.59/2.00    inference(ennf_transformation,[],[f20])).
% 11.59/2.00  
% 11.59/2.00  fof(f55,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(flattening,[],[f54])).
% 11.59/2.00  
% 11.59/2.00  fof(f105,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f55])).
% 11.59/2.00  
% 11.59/2.00  fof(f14,axiom,(
% 11.59/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f43,plain,(
% 11.59/2.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.59/2.00    inference(ennf_transformation,[],[f14])).
% 11.59/2.00  
% 11.59/2.00  fof(f44,plain,(
% 11.59/2.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(flattening,[],[f43])).
% 11.59/2.00  
% 11.59/2.00  fof(f62,plain,(
% 11.59/2.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.59/2.00    inference(nnf_transformation,[],[f44])).
% 11.59/2.00  
% 11.59/2.00  fof(f92,plain,(
% 11.59/2.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f62])).
% 11.59/2.00  
% 11.59/2.00  fof(f123,plain,(
% 11.59/2.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.59/2.00    inference(equality_resolution,[],[f92])).
% 11.59/2.00  
% 11.59/2.00  fof(f116,plain,(
% 11.59/2.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 11.59/2.00    inference(cnf_transformation,[],[f66])).
% 11.59/2.00  
% 11.59/2.00  fof(f106,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f57])).
% 11.59/2.00  
% 11.59/2.00  fof(f5,axiom,(
% 11.59/2.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f73,plain,(
% 11.59/2.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f5])).
% 11.59/2.00  
% 11.59/2.00  fof(f7,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f31,plain,(
% 11.59/2.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f7])).
% 11.59/2.00  
% 11.59/2.00  fof(f32,plain,(
% 11.59/2.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f31])).
% 11.59/2.00  
% 11.59/2.00  fof(f77,plain,(
% 11.59/2.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f32])).
% 11.59/2.00  
% 11.59/2.00  fof(f6,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f29,plain,(
% 11.59/2.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f6])).
% 11.59/2.00  
% 11.59/2.00  fof(f30,plain,(
% 11.59/2.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f29])).
% 11.59/2.00  
% 11.59/2.00  fof(f74,plain,(
% 11.59/2.00    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f30])).
% 11.59/2.00  
% 11.59/2.00  fof(f70,plain,(
% 11.59/2.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f28])).
% 11.59/2.00  
% 11.59/2.00  fof(f8,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f33,plain,(
% 11.59/2.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f8])).
% 11.59/2.00  
% 11.59/2.00  fof(f34,plain,(
% 11.59/2.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f33])).
% 11.59/2.00  
% 11.59/2.00  fof(f79,plain,(
% 11.59/2.00    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f34])).
% 11.59/2.00  
% 11.59/2.00  fof(f76,plain,(
% 11.59/2.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f32])).
% 11.59/2.00  
% 11.59/2.00  fof(f17,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f49,plain,(
% 11.59/2.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f17])).
% 11.59/2.00  
% 11.59/2.00  fof(f50,plain,(
% 11.59/2.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f49])).
% 11.59/2.00  
% 11.59/2.00  fof(f100,plain,(
% 11.59/2.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f50])).
% 11.59/2.00  
% 11.59/2.00  fof(f9,axiom,(
% 11.59/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f35,plain,(
% 11.59/2.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.59/2.00    inference(ennf_transformation,[],[f9])).
% 11.59/2.00  
% 11.59/2.00  fof(f36,plain,(
% 11.59/2.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.59/2.00    inference(flattening,[],[f35])).
% 11.59/2.00  
% 11.59/2.00  fof(f80,plain,(
% 11.59/2.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f36])).
% 11.59/2.00  
% 11.59/2.00  fof(f99,plain,(
% 11.59/2.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f50])).
% 11.59/2.00  
% 11.59/2.00  fof(f87,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f60])).
% 11.59/2.00  
% 11.59/2.00  fof(f119,plain,(
% 11.59/2.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.59/2.00    inference(equality_resolution,[],[f87])).
% 11.59/2.00  
% 11.59/2.00  fof(f1,axiom,(
% 11.59/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f67,plain,(
% 11.59/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f1])).
% 11.59/2.00  
% 11.59/2.00  fof(f18,axiom,(
% 11.59/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f51,plain,(
% 11.59/2.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.59/2.00    inference(ennf_transformation,[],[f18])).
% 11.59/2.00  
% 11.59/2.00  fof(f52,plain,(
% 11.59/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.59/2.00    inference(flattening,[],[f51])).
% 11.59/2.00  
% 11.59/2.00  fof(f102,plain,(
% 11.59/2.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f52])).
% 11.59/2.00  
% 11.59/2.00  fof(f94,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f46])).
% 11.59/2.00  
% 11.59/2.00  fof(f124,plain,(
% 11.59/2.00    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.59/2.00    inference(equality_resolution,[],[f94])).
% 11.59/2.00  
% 11.59/2.00  cnf(c_39,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.59/2.00      | ~ v1_funct_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1586,plain,
% 11.59/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.59/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_45,negated_conjecture,
% 11.59/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.59/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1582,plain,
% 11.59/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_37,plain,
% 11.59/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_48,negated_conjecture,
% 11.59/2.00      ( l1_struct_0(sK1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f110]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_536,plain,
% 11.59/2.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_37,c_48]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_537,plain,
% 11.59/2.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_536]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_49,negated_conjecture,
% 11.59/2.00      ( l1_struct_0(sK0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_541,plain,
% 11.59/2.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_37,c_49]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_542,plain,
% 11.59/2.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_541]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1615,plain,
% 11.59/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 11.59/2.00      inference(light_normalisation,[status(thm)],[c_1582,c_537,c_542]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_15,plain,
% 11.59/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1599,plain,
% 11.59/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2264,plain,
% 11.59/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1615,c_1599]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_44,negated_conjecture,
% 11.59/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f114]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1614,plain,
% 11.59/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.59/2.00      inference(light_normalisation,[status(thm)],[c_44,c_537,c_542]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2265,plain,
% 11.59/2.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_2264,c_1614]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2352,plain,
% 11.59/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_2265,c_2264]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_28,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.59/2.00      | ~ v2_funct_1(X0)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1592,plain,
% 11.59/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.59/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 11.59/2.00      | v2_funct_1(X2) != iProver_top
% 11.59/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6779,plain,
% 11.59/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 11.59/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v2_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2352,c_1592]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_47,negated_conjecture,
% 11.59/2.00      ( v1_funct_1(sK2) ),
% 11.59/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_52,plain,
% 11.59/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_43,negated_conjecture,
% 11.59/2.00      ( v2_funct_1(sK2) ),
% 11.59/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_55,plain,
% 11.59/2.00      ( v2_funct_1(sK2) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2354,plain,
% 11.59/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_2265,c_1615]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_46,negated_conjecture,
% 11.59/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 11.59/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1581,plain,
% 11.59/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1613,plain,
% 11.59/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 11.59/2.00      inference(light_normalisation,[status(thm)],[c_1581,c_537,c_542]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2355,plain,
% 11.59/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_2265,c_1613]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7140,plain,
% 11.59/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_6779,c_52,c_55,c_2354,c_2355]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_40,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1585,plain,
% 11.59/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.59/2.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 11.59/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_21,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.59/2.00      | k1_xboole_0 = X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1593,plain,
% 11.59/2.00      ( k1_relset_1(X0,X1,X2) = X0
% 11.59/2.00      | k1_xboole_0 = X1
% 11.59/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5343,plain,
% 11.59/2.00      ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = X0
% 11.59/2.00      | k1_xboole_0 = X1
% 11.59/2.00      | v1_funct_2(X2,X1,X0) != iProver_top
% 11.59/2.00      | v1_funct_2(k2_tops_2(X1,X0,X2),X0,X1) != iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 11.59/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1586,c_1593]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_9999,plain,
% 11.59/2.00      ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = X0
% 11.59/2.00      | k1_xboole_0 = X1
% 11.59/2.00      | v1_funct_2(X2,X1,X0) != iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 11.59/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1585,c_5343]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_10014,plain,
% 11.59/2.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = k2_struct_0(sK0)
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_7140,c_9999]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3,plain,
% 11.59/2.00      ( ~ v1_funct_1(X0)
% 11.59/2.00      | v1_funct_1(k2_funct_1(X0))
% 11.59/2.00      | ~ v1_relat_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1755,plain,
% 11.59/2.00      ( v1_funct_1(k2_funct_1(sK2))
% 11.59/2.00      | ~ v1_funct_1(sK2)
% 11.59/2.00      | ~ v1_relat_1(sK2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1756,plain,
% 11.59/2.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2,plain,
% 11.59/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.59/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1611,plain,
% 11.59/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1,plain,
% 11.59/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.59/2.00      | ~ v1_relat_1(X1)
% 11.59/2.00      | v1_relat_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1612,plain,
% 11.59/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.59/2.00      | v1_relat_1(X1) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2677,plain,
% 11.59/2.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 11.59/2.00      | v1_relat_1(sK2) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2354,c_1612]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2829,plain,
% 11.59/2.00      ( v1_relat_1(sK2) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1611,c_2677]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_29,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v2_funct_1(X0)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1591,plain,
% 11.59/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.59/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.59/2.00      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.59/2.00      | v2_funct_1(X2) != iProver_top
% 11.59/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6205,plain,
% 11.59/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 11.59/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v2_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2352,c_1591]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_11066,plain,
% 11.59/2.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = k2_struct_0(sK0)
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_10014,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_19,plain,
% 11.59/2.00      ( v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | k1_relset_1(X1,X2,X0) != X1
% 11.59/2.00      | k1_xboole_0 = X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1595,plain,
% 11.59/2.00      ( k1_relset_1(X0,X1,X2) != X0
% 11.59/2.00      | k1_xboole_0 = X1
% 11.59/2.00      | v1_funct_2(X2,X0,X1) = iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_11071,plain,
% 11.59/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_11066,c_1595]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_27,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | v1_partfun1(X0,X1)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | k1_xboole_0 = X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_23,plain,
% 11.59/2.00      ( ~ v1_partfun1(X0,X1)
% 11.59/2.00      | ~ v4_relat_1(X0,X1)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k1_relat_1(X0) = X1 ),
% 11.59/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_656,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ v4_relat_1(X0,X1)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k1_relat_1(X0) = X1
% 11.59/2.00      | k1_xboole_0 = X2 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_27,c_23]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_14,plain,
% 11.59/2.00      ( v4_relat_1(X0,X1)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.59/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_660,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k1_relat_1(X0) = X1
% 11.59/2.00      | k1_xboole_0 = X2 ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_656,c_14]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1576,plain,
% 11.59/2.00      ( k1_relat_1(X0) = X1
% 11.59/2.00      | k1_xboole_0 = X2
% 11.59/2.00      | v1_funct_2(X0,X1,X2) != iProver_top
% 11.59/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2615,plain,
% 11.59/2.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2354,c_1576]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2359,plain,
% 11.59/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 11.59/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2355]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2616,plain,
% 11.59/2.00      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 11.59/2.00      | ~ v1_funct_1(sK2)
% 11.59/2.00      | ~ v1_relat_1(sK2)
% 11.59/2.00      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.59/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2615]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2830,plain,
% 11.59/2.00      ( v1_relat_1(sK2) ),
% 11.59/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2829]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2832,plain,
% 11.59/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.00      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_2615,c_47,c_2359,c_2616,c_2830]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2833,plain,
% 11.59/2.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.59/2.00      inference(renaming,[status(thm)],[c_2832]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_38,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v2_funct_1(X0)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 11.59/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.59/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1587,plain,
% 11.59/2.00      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 11.59/2.00      | k2_relset_1(X0,X1,X2) != X1
% 11.59/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.59/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.59/2.00      | v2_funct_1(X2) != iProver_top
% 11.59/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5992,plain,
% 11.59/2.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 11.59/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v2_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2352,c_1587]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7063,plain,
% 11.59/2.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_5992,c_52,c_55,c_2354,c_2355]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_24,plain,
% 11.59/2.00      ( r2_funct_2(X0,X1,X2,X2)
% 11.59/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.59/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.59/2.00      | ~ v1_funct_1(X2) ),
% 11.59/2.00      inference(cnf_transformation,[],[f123]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_42,negated_conjecture,
% 11.59/2.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 11.59/2.00      inference(cnf_transformation,[],[f116]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_635,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 11.59/2.00      | u1_struct_0(sK1) != X2
% 11.59/2.00      | u1_struct_0(sK0) != X1
% 11.59/2.00      | sK2 != X0 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_24,c_42]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_636,plain,
% 11.59/2.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 11.59/2.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.59/2.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 11.59/2.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_635]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1577,plain,
% 11.59/2.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 11.59/2.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1616,plain,
% 11.59/2.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 11.59/2.00      inference(light_normalisation,[status(thm)],[c_1577,c_537,c_542]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2353,plain,
% 11.59/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_2265,c_1616]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7067,plain,
% 11.59/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.59/2.00      inference(demodulation,[status(thm)],[c_7063,c_2353]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_41,plain,
% 11.59/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 11.59/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1584,plain,
% 11.59/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.59/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7148,plain,
% 11.59/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 11.59/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_7140,c_1584]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7732,plain,
% 11.59/2.00      ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_7067,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,
% 11.59/2.00                 c_7148]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7733,plain,
% 11.59/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.00      inference(renaming,[status(thm)],[c_7732]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_7736,plain,
% 11.59/2.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 11.59/2.00      | k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2833,c_7733]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5,plain,
% 11.59/2.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 11.59/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1608,plain,
% 11.59/2.00      ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1583,plain,
% 11.59/2.00      ( v2_funct_1(sK2) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_9,plain,
% 11.59/2.00      ( ~ v2_funct_1(X0)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1604,plain,
% 11.59/2.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.59/2.00      | v2_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4006,plain,
% 11.59/2.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1583,c_1604]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4358,plain,
% 11.59/2.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_4006,c_52,c_2829]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_8,plain,
% 11.59/2.00      ( v2_funct_1(X0)
% 11.59/2.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 11.59/2.00      | ~ v1_funct_1(X1)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X1)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1605,plain,
% 11.59/2.00      ( k1_relat_1(X0) != k2_relat_1(X1)
% 11.59/2.00      | v2_funct_1(X1) = iProver_top
% 11.59/2.00      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 11.59/2.00      | v1_funct_1(X1) != iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_relat_1(X1) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6009,plain,
% 11.59/2.00      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 11.59/2.00      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 11.59/2.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) != iProver_top
% 11.59/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_4358,c_1605]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4,plain,
% 11.59/2.00      ( ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | v1_relat_1(k2_funct_1(X0)) ),
% 11.59/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3227,plain,
% 11.59/2.00      ( ~ v1_funct_1(sK2)
% 11.59/2.00      | v1_relat_1(k2_funct_1(sK2))
% 11.59/2.00      | ~ v1_relat_1(sK2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3228,plain,
% 11.59/2.00      ( v1_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_3227]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6628,plain,
% 11.59/2.00      ( v1_relat_1(X0) != iProver_top
% 11.59/2.00      | k1_relat_1(X0) != k1_relat_1(sK2)
% 11.59/2.00      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 11.59/2.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_6009,c_52,c_1756,c_2829,c_3228]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6629,plain,
% 11.59/2.00      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 11.59/2.00      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 11.59/2.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_funct_1(X0) != iProver_top
% 11.59/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.00      inference(renaming,[status(thm)],[c_6628]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6635,plain,
% 11.59/2.00      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 11.59/2.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.00      | v1_funct_1(sK2) != iProver_top
% 11.59/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.00      inference(equality_resolution,[status(thm)],[c_6629]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_11,plain,
% 11.59/2.00      ( ~ v2_funct_1(X0)
% 11.59/2.00      | ~ v1_funct_1(X0)
% 11.59/2.00      | ~ v1_relat_1(X0)
% 11.59/2.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 11.59/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1602,plain,
% 11.59/2.01      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 11.59/2.01      | v2_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4126,plain,
% 11.59/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1583,c_1602]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4480,plain,
% 11.59/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_4126,c_52,c_2829]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6636,plain,
% 11.59/2.01      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_6635,c_4480]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6639,plain,
% 11.59/2.01      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_6636,c_52,c_2829]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6643,plain,
% 11.59/2.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1608,c_6639]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_10,plain,
% 11.59/2.01      ( ~ v2_funct_1(X0)
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1603,plain,
% 11.59/2.01      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.59/2.01      | v2_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3369,plain,
% 11.59/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1583,c_1603]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3495,plain,
% 11.59/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_3369,c_52,c_2829]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31,plain,
% 11.59/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1589,plain,
% 11.59/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3497,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_3495,c_1589]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3585,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_3497,c_52,c_1756,c_2829,c_3228]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3590,plain,
% 11.59/2.01      ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_3585,c_1599]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4360,plain,
% 11.59/2.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_4358,c_3590]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_5993,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_4360,c_1587]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_13,plain,
% 11.59/2.01      ( ~ v2_funct_1(X0)
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 11.59/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1600,plain,
% 11.59/2.01      ( k2_funct_1(k2_funct_1(X0)) = X0
% 11.59/2.01      | v2_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3089,plain,
% 11.59/2.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1583,c_1600]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1843,plain,
% 11.59/2.01      ( ~ v2_funct_1(sK2)
% 11.59/2.01      | ~ v1_funct_1(sK2)
% 11.59/2.01      | ~ v1_relat_1(sK2)
% 11.59/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_13]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1844,plain,
% 11.59/2.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.59/2.01      | v2_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3375,plain,
% 11.59/2.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_3089,c_52,c_55,c_1844,c_2829]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_5994,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_5993,c_3375]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4361,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_4358,c_3585]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_32,plain,
% 11.59/2.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1588,plain,
% 11.59/2.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3498,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_3495,c_1588]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3502,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_3498,c_52,c_1756,c_2829,c_3228]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4362,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_4358,c_3502]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6574,plain,
% 11.59/2.01      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_5994,c_52,c_1756,c_2829,c_4361,c_4362]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6575,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(renaming,[status(thm)],[c_6574]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6790,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_6643,c_6575]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7737,plain,
% 11.59/2.01      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.01      | sK2 != sK2
% 11.59/2.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_7736,c_6790]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7738,plain,
% 11.59/2.01      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.01      inference(equality_resolution_simp,[status(thm)],[c_7737]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12844,plain,
% 11.59/2.01      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_11071,c_7738]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12848,plain,
% 11.59/2.01      ( k2_relat_1(sK2) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1586,c_12844]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12874,plain,
% 11.59/2.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_12848,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,
% 11.59/2.01                 c_6779]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12896,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_7140]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_17,plain,
% 11.59/2.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.59/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.59/2.01      | k1_xboole_0 = X1
% 11.59/2.01      | k1_xboole_0 = X0 ),
% 11.59/2.01      inference(cnf_transformation,[],[f119]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1597,plain,
% 11.59/2.01      ( k1_xboole_0 = X0
% 11.59/2.01      | k1_xboole_0 = X1
% 11.59/2.01      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_5347,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.59/2.01      | k1_xboole_0 = X0
% 11.59/2.01      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.59/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1586,c_1597]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_13411,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.59/2.01      | k1_xboole_0 = X0
% 11.59/2.01      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 11.59/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.59/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1585,c_5347]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_15063,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
% 11.59/2.01      | k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_12896,c_13411]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7134,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_6205,c_52,c_55,c_2354,c_2355]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12897,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_7134]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_26213,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = k1_xboole_0
% 11.59/2.01      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_15063,c_52,c_1756,c_2829,c_12897]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12915,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_2354]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_13732,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_12915,c_1597]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12917,plain,
% 11.59/2.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_2355]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_14061,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0 | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_13732,c_12917]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_14062,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 11.59/2.01      inference(renaming,[status(thm)],[c_14061]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7147,plain,
% 11.59/2.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_7140,c_1599]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7150,plain,
% 11.59/2.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_7147,c_4358]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7372,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 11.59/2.01      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_7150,c_1587]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7373,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_7372,c_3375]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7728,plain,
% 11.59/2.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_7373,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205,
% 11.59/2.01                 c_6643,c_6779]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12892,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_7728]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_14063,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | k1_relat_1(sK2) != k1_xboole_0
% 11.59/2.01      | sK2 = k1_xboole_0 ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_14062,c_12892]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_0,plain,
% 11.59/2.01      ( r1_tarski(k1_xboole_0,X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_35,plain,
% 11.59/2.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.59/2.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f102]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_548,plain,
% 11.59/2.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | X1 != X2
% 11.59/2.01      | k2_relat_1(X0) != k1_xboole_0 ),
% 11.59/2.01      inference(resolution_lifted,[status(thm)],[c_0,c_35]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_549,plain,
% 11.59/2.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | k2_relat_1(X0) != k1_xboole_0 ),
% 11.59/2.01      inference(unflattening,[status(thm)],[c_548]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2123,plain,
% 11.59/2.01      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 11.59/2.01      | ~ v1_funct_1(sK2)
% 11.59/2.01      | ~ v1_relat_1(sK2)
% 11.59/2.01      | k2_relat_1(sK2) != k1_xboole_0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_549]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2124,plain,
% 11.59/2.01      ( k2_relat_1(sK2) != k1_xboole_0
% 11.59/2.01      | v1_funct_2(sK2,k1_relat_1(sK2),X0) = iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2126,plain,
% 11.59/2.01      ( k2_relat_1(sK2) != k1_xboole_0
% 11.59/2.01      | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_2124]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6780,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_4360,c_1592]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6781,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.59/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 11.59/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_6780,c_3375]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3460,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 11.59/2.01      | ~ v1_funct_1(sK2)
% 11.59/2.01      | ~ v1_relat_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_31]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3461,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_3460]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_6907,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_6781,c_52,c_2829,c_3461]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12900,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_6907]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_13655,plain,
% 11.59/2.01      ( k1_relat_1(sK2) = k1_xboole_0
% 11.59/2.01      | sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_12900,c_1597]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_16524,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.59/2.01      | sK2 = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_14063,c_52,c_55,c_1756,c_2126,c_2354,c_2355,c_2829,
% 11.59/2.01                 c_6205,c_6779,c_12848,c_13655]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12891,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_7733]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_16532,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_16524,c_12891]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23247,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_16524,c_16532]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23333,plain,
% 11.59/2.01      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | sK2 = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_23247,c_12915]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23334,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(renaming,[status(thm)],[c_23333]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23338,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_16524,c_23334]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23337,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1585,c_23334]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23345,plain,
% 11.59/2.01      ( sK2 = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_23338,c_52,c_1756,c_2829,c_12896,c_12897,c_23337]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_26215,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.59/2.01      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_26213,c_23345]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_5342,plain,
% 11.59/2.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.59/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_tops_2(X1,X2,X0)) = iProver_top
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(X2,X1)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1586,c_1612]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_9062,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_7140,c_5342]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_9822,plain,
% 11.59/2.01      ( v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_9062,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12883,plain,
% 11.59/2.01      ( v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_9822]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7982,plain,
% 11.59/2.01      ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_7148,c_52,c_55,c_1756,c_2354,c_2355,c_2829,c_6205]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1610,plain,
% 11.59/2.01      ( v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3016,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1589,c_1599]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3817,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1610,c_3016]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_162,plain,
% 11.59/2.01      ( v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7379,plain,
% 11.59/2.01      ( v1_relat_1(X0) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0)) ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_3817,c_162]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7380,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(renaming,[status(thm)],[c_7379]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7988,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))))
% 11.59/2.01      | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_7982,c_7380]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_15172,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))))
% 11.59/2.01      | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_7988,c_12874]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_19415,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))))
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_12883,c_15172]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30017,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))))
% 11.59/2.01      | v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_19415,c_23345]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30019,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))),k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1611,c_30017]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30277,plain,
% 11.59/2.01      ( k2_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))))
% 11.59/2.01      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_26215,c_30019]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12909,plain,
% 11.59/2.01      ( k2_relset_1(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_4360]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23395,plain,
% 11.59/2.01      ( k2_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12909]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12913,plain,
% 11.59/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_3495]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23404,plain,
% 11.59/2.01      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12913]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23410,plain,
% 11.59/2.01      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_4358]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30284,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | k2_relat_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k1_relat_1(k1_xboole_0) ),
% 11.59/2.01      inference(light_normalisation,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_30277,c_23395,c_23404,c_23410]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_976,plain,( X0 = X0 ),theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1013,plain,
% 11.59/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_976]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_977,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1745,plain,
% 11.59/2.01      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_977]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1746,plain,
% 11.59/2.01      ( sK2 != k1_xboole_0
% 11.59/2.01      | k1_xboole_0 = sK2
% 11.59/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_1745]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_983,plain,
% 11.59/2.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.59/2.01      theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3191,plain,
% 11.59/2.01      ( v1_funct_1(X0)
% 11.59/2.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 11.59/2.01      | X0 != k2_funct_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_983]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3909,plain,
% 11.59/2.01      ( v1_funct_1(k2_funct_1(X0))
% 11.59/2.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 11.59/2.01      | k2_funct_1(X0) != k2_funct_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_3191]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3910,plain,
% 11.59/2.01      ( k2_funct_1(X0) != k2_funct_1(sK2)
% 11.59/2.01      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_3909]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3912,plain,
% 11.59/2.01      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
% 11.59/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_3910]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_982,plain,
% 11.59/2.01      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 11.59/2.01      theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7156,plain,
% 11.59/2.01      ( X0 != sK2 | k2_funct_1(X0) = k2_funct_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_982]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7157,plain,
% 11.59/2.01      ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2) | k1_xboole_0 != sK2 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_7156]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23379,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12896]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23382,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12897]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23378,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12891]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_26225,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_26215,c_23378]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_29911,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1586,c_26225]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23394,plain,
% 11.59/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12915]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_29912,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_26215,c_26225]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30864,plain,
% 11.59/2.01      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.59/2.01      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_29911,c_23394,c_29912]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30865,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(renaming,[status(thm)],[c_30864]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30868,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_1585,c_30865]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31248,plain,
% 11.59/2.01      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_30284,c_52,c_1013,c_1746,c_1756,c_2829,c_3912,c_7157,
% 11.59/2.01                 c_12896,c_12897,c_23337,c_23379,c_23382,c_30868]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31268,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 11.59/2.01      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_31248,c_23378]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_53,plain,
% 11.59/2.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_54,plain,
% 11.59/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_134,plain,
% 11.59/2.01      ( v4_relat_1(X0,X1) = iProver_top
% 11.59/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_136,plain,
% 11.59/2.01      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 11.59/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_134]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_26,plain,
% 11.59/2.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.59/2.01      | v1_partfun1(X0,k1_xboole_0)
% 11.59/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.59/2.01      | ~ v1_funct_1(X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f124]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_687,plain,
% 11.59/2.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.59/2.01      | ~ v4_relat_1(X2,X3)
% 11.59/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X2)
% 11.59/2.01      | X0 != X2
% 11.59/2.01      | k1_relat_1(X2) = X3
% 11.59/2.01      | k1_xboole_0 != X3 ),
% 11.59/2.01      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_688,plain,
% 11.59/2.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.59/2.01      | ~ v4_relat_1(X0,k1_xboole_0)
% 11.59/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.59/2.01      | ~ v1_funct_1(X0)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 11.59/2.01      inference(unflattening,[status(thm)],[c_687]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_689,plain,
% 11.59/2.01      ( k1_relat_1(X0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 11.59/2.01      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.59/2.01      | v1_funct_1(X0) != iProver_top
% 11.59/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_691,plain,
% 11.59/2.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 11.59/2.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.59/2.01      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.59/2.01      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.59/2.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_689]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1726,plain,
% 11.59/2.01      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_983]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1727,plain,
% 11.59/2.01      ( X0 != sK2
% 11.59/2.01      | v1_funct_1(X0) = iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1729,plain,
% 11.59/2.01      ( k1_xboole_0 != sK2
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_1727]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2911,plain,
% 11.59/2.01      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_977]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2912,plain,
% 11.59/2.01      ( u1_struct_0(sK1) != k1_xboole_0
% 11.59/2.01      | k1_xboole_0 = u1_struct_0(sK1)
% 11.59/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_2911]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_978,plain,
% 11.59/2.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.59/2.01      theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3159,plain,
% 11.59/2.01      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_978]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3174,plain,
% 11.59/2.01      ( X0 != sK2
% 11.59/2.01      | v1_relat_1(X0) = iProver_top
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_3159]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3176,plain,
% 11.59/2.01      ( k1_xboole_0 != sK2
% 11.59/2.01      | v1_relat_1(sK2) != iProver_top
% 11.59/2.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_3174]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2561,plain,
% 11.59/2.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 11.59/2.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.59/2.01      | u1_struct_0(sK1) != X0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_977]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3398,plain,
% 11.59/2.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.59/2.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 11.59/2.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_2561]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4110,plain,
% 11.59/2.01      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_977]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7580,plain,
% 11.59/2.01      ( X0 = u1_struct_0(sK0)
% 11.59/2.01      | X0 != k2_struct_0(sK0)
% 11.59/2.01      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_4110]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_7581,plain,
% 11.59/2.01      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 11.59/2.01      | k1_xboole_0 = u1_struct_0(sK0)
% 11.59/2.01      | k1_xboole_0 != k2_struct_0(sK0) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_7580]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_4145,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 11.59/2.01      | ~ v1_funct_2(sK2,X1,X0)
% 11.59/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.59/2.01      | ~ v2_funct_1(sK2)
% 11.59/2.01      | ~ v1_funct_1(sK2)
% 11.59/2.01      | k2_relset_1(X1,X0,sK2) != X0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_29]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_8117,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 11.59/2.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.59/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.59/2.01      | ~ v2_funct_1(sK2)
% 11.59/2.01      | ~ v1_funct_1(sK2)
% 11.59/2.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_4145]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_8118,plain,
% 11.59/2.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 11.59/2.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.59/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.59/2.01      | v2_funct_1(sK2) != iProver_top
% 11.59/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_8117]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11508,plain,
% 11.59/2.01      ( ~ v1_funct_2(k2_funct_1(X0),X1,X2)
% 11.59/2.01      | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.59/2.01      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.59/2.01      | ~ v1_funct_1(k2_funct_1(X0)) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_39]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11509,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(X0),X1,X2) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_11508]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11511,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 11.59/2.01      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 11.59/2.01      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.59/2.01      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_11509]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_990,plain,
% 11.59/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.59/2.01      | v1_funct_2(X3,X4,X5)
% 11.59/2.01      | X3 != X0
% 11.59/2.01      | X4 != X1
% 11.59/2.01      | X5 != X2 ),
% 11.59/2.01      theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11528,plain,
% 11.59/2.01      ( v1_funct_2(X0,X1,X2)
% 11.59/2.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.59/2.01      | X2 != u1_struct_0(sK1)
% 11.59/2.01      | X1 != u1_struct_0(sK0)
% 11.59/2.01      | X0 != sK2 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_990]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11529,plain,
% 11.59/2.01      ( X0 != u1_struct_0(sK1)
% 11.59/2.01      | X1 != u1_struct_0(sK0)
% 11.59/2.01      | X2 != sK2
% 11.59/2.01      | v1_funct_2(X2,X1,X0) = iProver_top
% 11.59/2.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_11528]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11531,plain,
% 11.59/2.01      ( k1_xboole_0 != u1_struct_0(sK1)
% 11.59/2.01      | k1_xboole_0 != u1_struct_0(sK0)
% 11.59/2.01      | k1_xboole_0 != sK2
% 11.59/2.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.59/2.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_11529]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12204,plain,
% 11.59/2.01      ( X0 != X1 | X0 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_977]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12205,plain,
% 11.59/2.01      ( k2_struct_0(sK0) != k1_xboole_0
% 11.59/2.01      | k1_xboole_0 = k2_struct_0(sK0)
% 11.59/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_12204]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_2356,plain,
% 11.59/2.01      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_2265,c_537]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_12918,plain,
% 11.59/2.01      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_12874,c_2356]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_11571,plain,
% 11.59/2.01      ( v1_funct_2(X0,X1,X2)
% 11.59/2.01      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 11.59/2.01      | X1 != u1_struct_0(sK1)
% 11.59/2.01      | X2 != u1_struct_0(sK0)
% 11.59/2.01      | X0 != k2_funct_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_990]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_24877,plain,
% 11.59/2.01      ( v1_funct_2(k2_funct_1(X0),X1,X2)
% 11.59/2.01      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 11.59/2.01      | X1 != u1_struct_0(sK1)
% 11.59/2.01      | X2 != u1_struct_0(sK0)
% 11.59/2.01      | k2_funct_1(X0) != k2_funct_1(sK2) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_11571]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_24878,plain,
% 11.59/2.01      ( X0 != u1_struct_0(sK1)
% 11.59/2.01      | X1 != u1_struct_0(sK0)
% 11.59/2.01      | k2_funct_1(X2) != k2_funct_1(sK2)
% 11.59/2.01      | v1_funct_2(k2_funct_1(X2),X0,X1) = iProver_top
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_24877]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_24880,plain,
% 11.59/2.01      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
% 11.59/2.01      | k1_xboole_0 != u1_struct_0(sK1)
% 11.59/2.01      | k1_xboole_0 != u1_struct_0(sK0)
% 11.59/2.01      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 11.59/2.01      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_24878]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31269,plain,
% 11.59/2.01      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_31248,c_23379]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23391,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.59/2.01      | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_23345,c_12892]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31272,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.59/2.01      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_31248,c_23391]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_31275,plain,
% 11.59/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_31248,c_23394]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_34171,plain,
% 11.59/2.01      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_31268,c_52,c_53,c_54,c_44,c_55,c_136,c_537,c_542,
% 11.59/2.01                 c_691,c_1013,c_1729,c_1746,c_1756,c_2829,c_2912,c_3176,
% 11.59/2.01                 c_3398,c_3912,c_7157,c_7581,c_8118,c_11511,c_11531,
% 11.59/2.01                 c_12205,c_12896,c_12897,c_12918,c_23337,c_23379,c_23382,
% 11.59/2.01                 c_24880,c_30868,c_31269,c_31272,c_31275]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_33793,plain,
% 11.59/2.01      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 11.59/2.01      inference(global_propositional_subsumption,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_31272,c_52,c_53,c_136,c_542,c_691,c_1013,c_1729,
% 11.59/2.01                 c_1746,c_1756,c_2829,c_2912,c_3176,c_3912,c_7157,c_7581,
% 11.59/2.01                 c_11531,c_12205,c_12896,c_12897,c_12918,c_23337,c_23379,
% 11.59/2.01                 c_23382,c_30868,c_31275]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_34175,plain,
% 11.59/2.01      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_34171,c_33793]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(contradiction,plain,
% 11.59/2.01      ( $false ),
% 11.59/2.01      inference(minisat,
% 11.59/2.01                [status(thm)],
% 11.59/2.01                [c_34175,c_30868,c_23382,c_23379,c_23337,c_12918,c_12897,
% 11.59/2.01                 c_12896,c_12205,c_11531,c_7581,c_7157,c_3912,c_2912,
% 11.59/2.01                 c_2829,c_1756,c_1746,c_1013,c_542,c_53,c_52]) ).
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.59/2.01  
% 11.59/2.01  ------                               Statistics
% 11.59/2.01  
% 11.59/2.01  ------ General
% 11.59/2.01  
% 11.59/2.01  abstr_ref_over_cycles:                  0
% 11.59/2.01  abstr_ref_under_cycles:                 0
% 11.59/2.01  gc_basic_clause_elim:                   0
% 11.59/2.01  forced_gc_time:                         0
% 11.59/2.01  parsing_time:                           0.017
% 11.59/2.01  unif_index_cands_time:                  0.
% 11.59/2.01  unif_index_add_time:                    0.
% 11.59/2.01  orderings_time:                         0.
% 11.59/2.01  out_proof_time:                         0.035
% 11.59/2.01  total_time:                             1.156
% 11.59/2.01  num_of_symbols:                         57
% 11.59/2.01  num_of_terms:                           29434
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing
% 11.59/2.01  
% 11.59/2.01  num_of_splits:                          0
% 11.59/2.01  num_of_split_atoms:                     0
% 11.59/2.01  num_of_reused_defs:                     0
% 11.59/2.01  num_eq_ax_congr_red:                    9
% 11.59/2.01  num_of_sem_filtered_clauses:            1
% 11.59/2.01  num_of_subtypes:                        0
% 11.59/2.01  monotx_restored_types:                  0
% 11.59/2.01  sat_num_of_epr_types:                   0
% 11.59/2.01  sat_num_of_non_cyclic_types:            0
% 11.59/2.01  sat_guarded_non_collapsed_types:        0
% 11.59/2.01  num_pure_diseq_elim:                    0
% 11.59/2.01  simp_replaced_by:                       0
% 11.59/2.01  res_preprocessed:                       210
% 11.59/2.01  prep_upred:                             0
% 11.59/2.01  prep_unflattend:                        17
% 11.59/2.01  smt_new_axioms:                         0
% 11.59/2.01  pred_elim_cands:                        5
% 11.59/2.01  pred_elim:                              5
% 11.59/2.01  pred_elim_cl:                           7
% 11.59/2.01  pred_elim_cycles:                       8
% 11.59/2.01  merged_defs:                            0
% 11.59/2.01  merged_defs_ncl:                        0
% 11.59/2.01  bin_hyper_res:                          0
% 11.59/2.01  prep_cycles:                            4
% 11.59/2.01  pred_elim_time:                         0.006
% 11.59/2.01  splitting_time:                         0.
% 11.59/2.01  sem_filter_time:                        0.
% 11.59/2.01  monotx_time:                            0.001
% 11.59/2.01  subtype_inf_time:                       0.
% 11.59/2.01  
% 11.59/2.01  ------ Problem properties
% 11.59/2.01  
% 11.59/2.01  clauses:                                41
% 11.59/2.01  conjectures:                            5
% 11.59/2.01  epr:                                    2
% 11.59/2.01  horn:                                   36
% 11.59/2.01  ground:                                 8
% 11.59/2.01  unary:                                  10
% 11.59/2.01  binary:                                 1
% 11.59/2.01  lits:                                   141
% 11.59/2.01  lits_eq:                                31
% 11.59/2.01  fd_pure:                                0
% 11.59/2.01  fd_pseudo:                              0
% 11.59/2.01  fd_cond:                                3
% 11.59/2.01  fd_pseudo_cond:                         1
% 11.59/2.01  ac_symbols:                             0
% 11.59/2.01  
% 11.59/2.01  ------ Propositional Solver
% 11.59/2.01  
% 11.59/2.01  prop_solver_calls:                      35
% 11.59/2.01  prop_fast_solver_calls:                 4385
% 11.59/2.01  smt_solver_calls:                       0
% 11.59/2.01  smt_fast_solver_calls:                  0
% 11.59/2.01  prop_num_of_clauses:                    14569
% 11.59/2.01  prop_preprocess_simplified:             28258
% 11.59/2.01  prop_fo_subsumed:                       799
% 11.59/2.01  prop_solver_time:                       0.
% 11.59/2.01  smt_solver_time:                        0.
% 11.59/2.01  smt_fast_solver_time:                   0.
% 11.59/2.01  prop_fast_solver_time:                  0.
% 11.59/2.01  prop_unsat_core_time:                   0.002
% 11.59/2.01  
% 11.59/2.01  ------ QBF
% 11.59/2.01  
% 11.59/2.01  qbf_q_res:                              0
% 11.59/2.01  qbf_num_tautologies:                    0
% 11.59/2.01  qbf_prep_cycles:                        0
% 11.59/2.01  
% 11.59/2.01  ------ BMC1
% 11.59/2.01  
% 11.59/2.01  bmc1_current_bound:                     -1
% 11.59/2.01  bmc1_last_solved_bound:                 -1
% 11.59/2.01  bmc1_unsat_core_size:                   -1
% 11.59/2.01  bmc1_unsat_core_parents_size:           -1
% 11.59/2.01  bmc1_merge_next_fun:                    0
% 11.59/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.59/2.01  
% 11.59/2.01  ------ Instantiation
% 11.59/2.01  
% 11.59/2.01  inst_num_of_clauses:                    4388
% 11.59/2.01  inst_num_in_passive:                    1084
% 11.59/2.01  inst_num_in_active:                     1843
% 11.59/2.01  inst_num_in_unprocessed:                1461
% 11.59/2.01  inst_num_of_loops:                      2090
% 11.59/2.01  inst_num_of_learning_restarts:          0
% 11.59/2.01  inst_num_moves_active_passive:          243
% 11.59/2.01  inst_lit_activity:                      0
% 11.59/2.01  inst_lit_activity_moves:                1
% 11.59/2.01  inst_num_tautologies:                   0
% 11.59/2.01  inst_num_prop_implied:                  0
% 11.59/2.01  inst_num_existing_simplified:           0
% 11.59/2.01  inst_num_eq_res_simplified:             0
% 11.59/2.01  inst_num_child_elim:                    0
% 11.59/2.01  inst_num_of_dismatching_blockings:      1920
% 11.59/2.01  inst_num_of_non_proper_insts:           4173
% 11.59/2.01  inst_num_of_duplicates:                 0
% 11.59/2.01  inst_inst_num_from_inst_to_res:         0
% 11.59/2.01  inst_dismatching_checking_time:         0.
% 11.59/2.01  
% 11.59/2.01  ------ Resolution
% 11.59/2.01  
% 11.59/2.01  res_num_of_clauses:                     0
% 11.59/2.01  res_num_in_passive:                     0
% 11.59/2.01  res_num_in_active:                      0
% 11.59/2.01  res_num_of_loops:                       214
% 11.59/2.01  res_forward_subset_subsumed:            121
% 11.59/2.01  res_backward_subset_subsumed:           0
% 11.59/2.01  res_forward_subsumed:                   0
% 11.59/2.01  res_backward_subsumed:                  0
% 11.59/2.01  res_forward_subsumption_resolution:     1
% 11.59/2.01  res_backward_subsumption_resolution:    0
% 11.59/2.01  res_clause_to_clause_subsumption:       4188
% 11.59/2.01  res_orphan_elimination:                 0
% 11.59/2.01  res_tautology_del:                      257
% 11.59/2.01  res_num_eq_res_simplified:              0
% 11.59/2.01  res_num_sel_changes:                    0
% 11.59/2.01  res_moves_from_active_to_pass:          0
% 11.59/2.01  
% 11.59/2.01  ------ Superposition
% 11.59/2.01  
% 11.59/2.01  sup_time_total:                         0.
% 11.59/2.01  sup_time_generating:                    0.
% 11.59/2.01  sup_time_sim_full:                      0.
% 11.59/2.01  sup_time_sim_immed:                     0.
% 11.59/2.01  
% 11.59/2.01  sup_num_of_clauses:                     594
% 11.59/2.01  sup_num_in_active:                      167
% 11.59/2.01  sup_num_in_passive:                     427
% 11.59/2.01  sup_num_of_loops:                       417
% 11.59/2.01  sup_fw_superposition:                   791
% 11.59/2.01  sup_bw_superposition:                   983
% 11.59/2.01  sup_immediate_simplified:               766
% 11.59/2.01  sup_given_eliminated:                   10
% 11.59/2.01  comparisons_done:                       0
% 11.59/2.01  comparisons_avoided:                    256
% 11.59/2.01  
% 11.59/2.01  ------ Simplifications
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  sim_fw_subset_subsumed:                 236
% 11.59/2.01  sim_bw_subset_subsumed:                 165
% 11.59/2.01  sim_fw_subsumed:                        99
% 11.59/2.01  sim_bw_subsumed:                        36
% 11.59/2.01  sim_fw_subsumption_res:                 0
% 11.59/2.01  sim_bw_subsumption_res:                 0
% 11.59/2.01  sim_tautology_del:                      17
% 11.59/2.01  sim_eq_tautology_del:                   448
% 11.59/2.01  sim_eq_res_simp:                        3
% 11.59/2.01  sim_fw_demodulated:                     4
% 11.59/2.01  sim_bw_demodulated:                     163
% 11.59/2.01  sim_light_normalised:                   552
% 11.59/2.01  sim_joinable_taut:                      0
% 11.59/2.01  sim_joinable_simp:                      0
% 11.59/2.01  sim_ac_normalised:                      0
% 11.59/2.01  sim_smt_subsumption:                    0
% 11.59/2.01  
%------------------------------------------------------------------------------
