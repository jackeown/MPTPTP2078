%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:45 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  207 (9675 expanded)
%              Number of clauses        :  142 (2567 expanded)
%              Number of leaves         :   17 (2980 expanded)
%              Depth                    :   26
%              Number of atoms          :  741 (68634 expanded)
%              Number of equality atoms :  381 (25363 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
                 => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
            | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2))
          | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2))
              | k1_partfun1(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).

fof(f66,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
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

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_308,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_309,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_313,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_314,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_1190,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_23,c_309,c_314])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_446,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_447,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_451,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_26])).

cnf(c_452,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_1160,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_1890,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1160])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1168,c_309,c_314])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1167,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1187,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1167,c_309,c_314])).

cnf(c_2261,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1890,c_1193,c_1187])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1170,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2267,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2261,c_1170])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1176,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2268,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2261,c_1176])).

cnf(c_2271,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2267,c_2268])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_423,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_26])).

cnf(c_428,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_1161,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1764,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1161])).

cnf(c_3861,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2271,c_1193,c_1187,c_1764])).

cnf(c_3862,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_3861])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1559,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1178])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1474,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1561,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1562,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_2572,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_33,c_1474,c_1562])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_498,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_499,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_501,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_26])).

cnf(c_1157,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_2577,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2572,c_1157])).

cnf(c_3863,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3862,c_2577])).

cnf(c_3876,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3863,c_2261])).

cnf(c_2174,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1170])).

cnf(c_3122,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_1187])).

cnf(c_3123,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3122])).

cnf(c_1554,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1193,c_1176])).

cnf(c_3124,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3123,c_1554])).

cnf(c_3133,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_1187])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_372,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_26])).

cnf(c_377,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_1163,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_484,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_485,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_487,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_26])).

cnf(c_1158,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_1614,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1158,c_26,c_24,c_485,c_1473,c_1561])).

cnf(c_1893,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1163,c_1614])).

cnf(c_1900,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k6_partfun1(k2_struct_0(sK1)) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1893])).

cnf(c_2374,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k6_partfun1(k2_struct_0(sK1)) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1900,c_1193,c_1187])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1169,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2883,plain,
    ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1169])).

cnf(c_3524,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2883,c_31])).

cnf(c_3525,plain,
    ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3524])).

cnf(c_3534,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2261,c_3525])).

cnf(c_3537,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3534,c_1614])).

cnf(c_32,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_399,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_403,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_26])).

cnf(c_404,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_1384,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_1385,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_735,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1442,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_1589,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_3744,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3537,c_32,c_33,c_23,c_309,c_1385,c_1589])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_320,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_321,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_325,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_26])).

cnf(c_326,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_1165,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1825,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1165])).

cnf(c_1828,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1825,c_1193,c_1187])).

cnf(c_21,negated_conjecture,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1326,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_21,c_309,c_314,c_1190])).

cnf(c_1831,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_1828,c_1326])).

cnf(c_2472,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_1554,c_1831])).

cnf(c_3747,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k6_partfun1(k2_struct_0(sK1)) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_3744,c_2472])).

cnf(c_2884,plain,
    ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2261,c_1169])).

cnf(c_3751,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_32,c_33,c_23,c_309,c_1385,c_1589])).

cnf(c_3752,plain,
    ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3751])).

cnf(c_3760,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_3752])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_470,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_471,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_473,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_26])).

cnf(c_1159,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_1659,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_26,c_24,c_471,c_1473,c_1561])).

cnf(c_3768,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3760,c_1659])).

cnf(c_4150,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_31,c_2374,c_3747,c_3768])).

cnf(c_5374,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3876,c_4150])).

cnf(c_5381,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5374,c_1176])).

cnf(c_5403,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5381,c_2577])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1171,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5383,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5374,c_1171])).

cnf(c_1767,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_1193,c_1187])).

cnf(c_3878,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3863,c_1767])).

cnf(c_5082,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3878,c_4150])).

cnf(c_5503,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5383,c_5082])).

cnf(c_5504,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5503])).

cnf(c_5828,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5403,c_5504])).

cnf(c_6551,plain,
    ( k6_partfun1(k2_struct_0(sK1)) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3747,c_31,c_3768])).

cnf(c_6553,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6551,c_4150])).

cnf(c_6650,plain,
    ( k6_partfun1(k1_xboole_0) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5828,c_6553])).

cnf(c_6675,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6650])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.94/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/0.98  
% 2.94/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/0.98  
% 2.94/0.98  ------  iProver source info
% 2.94/0.98  
% 2.94/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.94/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/0.98  git: non_committed_changes: false
% 2.94/0.98  git: last_make_outside_of_git: false
% 2.94/0.98  
% 2.94/0.98  ------ 
% 2.94/0.98  
% 2.94/0.98  ------ Input Options
% 2.94/0.98  
% 2.94/0.98  --out_options                           all
% 2.94/0.98  --tptp_safe_out                         true
% 2.94/0.98  --problem_path                          ""
% 2.94/0.98  --include_path                          ""
% 2.94/0.98  --clausifier                            res/vclausify_rel
% 2.94/0.98  --clausifier_options                    --mode clausify
% 2.94/0.98  --stdin                                 false
% 2.94/0.98  --stats_out                             all
% 2.94/0.98  
% 2.94/0.98  ------ General Options
% 2.94/0.98  
% 2.94/0.98  --fof                                   false
% 2.94/0.98  --time_out_real                         305.
% 2.94/0.98  --time_out_virtual                      -1.
% 2.94/0.98  --symbol_type_check                     false
% 2.94/0.98  --clausify_out                          false
% 2.94/0.98  --sig_cnt_out                           false
% 2.94/0.98  --trig_cnt_out                          false
% 2.94/0.98  --trig_cnt_out_tolerance                1.
% 2.94/0.98  --trig_cnt_out_sk_spl                   false
% 2.94/0.98  --abstr_cl_out                          false
% 2.94/0.98  
% 2.94/0.98  ------ Global Options
% 2.94/0.98  
% 2.94/0.98  --schedule                              default
% 2.94/0.98  --add_important_lit                     false
% 2.94/0.98  --prop_solver_per_cl                    1000
% 2.94/0.98  --min_unsat_core                        false
% 2.94/0.98  --soft_assumptions                      false
% 2.94/0.98  --soft_lemma_size                       3
% 2.94/0.98  --prop_impl_unit_size                   0
% 2.94/0.98  --prop_impl_unit                        []
% 2.94/0.98  --share_sel_clauses                     true
% 2.94/0.98  --reset_solvers                         false
% 2.94/0.98  --bc_imp_inh                            [conj_cone]
% 2.94/0.98  --conj_cone_tolerance                   3.
% 2.94/0.98  --extra_neg_conj                        none
% 2.94/0.98  --large_theory_mode                     true
% 2.94/0.98  --prolific_symb_bound                   200
% 2.94/0.98  --lt_threshold                          2000
% 2.94/0.98  --clause_weak_htbl                      true
% 2.94/0.98  --gc_record_bc_elim                     false
% 2.94/0.98  
% 2.94/0.98  ------ Preprocessing Options
% 2.94/0.98  
% 2.94/0.98  --preprocessing_flag                    true
% 2.94/0.98  --time_out_prep_mult                    0.1
% 2.94/0.98  --splitting_mode                        input
% 2.94/0.98  --splitting_grd                         true
% 2.94/0.98  --splitting_cvd                         false
% 2.94/0.98  --splitting_cvd_svl                     false
% 2.94/0.98  --splitting_nvd                         32
% 2.94/0.98  --sub_typing                            true
% 2.94/0.98  --prep_gs_sim                           true
% 2.94/0.98  --prep_unflatten                        true
% 2.94/0.98  --prep_res_sim                          true
% 2.94/0.98  --prep_upred                            true
% 2.94/0.98  --prep_sem_filter                       exhaustive
% 2.94/0.98  --prep_sem_filter_out                   false
% 2.94/0.98  --pred_elim                             true
% 2.94/0.98  --res_sim_input                         true
% 2.94/0.98  --eq_ax_congr_red                       true
% 2.94/0.98  --pure_diseq_elim                       true
% 2.94/0.98  --brand_transform                       false
% 2.94/0.98  --non_eq_to_eq                          false
% 2.94/0.98  --prep_def_merge                        true
% 2.94/0.98  --prep_def_merge_prop_impl              false
% 2.94/0.98  --prep_def_merge_mbd                    true
% 2.94/0.98  --prep_def_merge_tr_red                 false
% 2.94/0.98  --prep_def_merge_tr_cl                  false
% 2.94/0.98  --smt_preprocessing                     true
% 2.94/0.98  --smt_ac_axioms                         fast
% 2.94/0.98  --preprocessed_out                      false
% 2.94/0.98  --preprocessed_stats                    false
% 2.94/0.98  
% 2.94/0.98  ------ Abstraction refinement Options
% 2.94/0.98  
% 2.94/0.98  --abstr_ref                             []
% 2.94/0.98  --abstr_ref_prep                        false
% 2.94/0.98  --abstr_ref_until_sat                   false
% 2.94/0.98  --abstr_ref_sig_restrict                funpre
% 2.94/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.98  --abstr_ref_under                       []
% 2.94/0.98  
% 2.94/0.98  ------ SAT Options
% 2.94/0.98  
% 2.94/0.98  --sat_mode                              false
% 2.94/0.98  --sat_fm_restart_options                ""
% 2.94/0.98  --sat_gr_def                            false
% 2.94/0.98  --sat_epr_types                         true
% 2.94/0.98  --sat_non_cyclic_types                  false
% 2.94/0.98  --sat_finite_models                     false
% 2.94/0.98  --sat_fm_lemmas                         false
% 2.94/0.98  --sat_fm_prep                           false
% 2.94/0.98  --sat_fm_uc_incr                        true
% 2.94/0.98  --sat_out_model                         small
% 2.94/0.98  --sat_out_clauses                       false
% 2.94/0.98  
% 2.94/0.98  ------ QBF Options
% 2.94/0.98  
% 2.94/0.98  --qbf_mode                              false
% 2.94/0.98  --qbf_elim_univ                         false
% 2.94/0.98  --qbf_dom_inst                          none
% 2.94/0.98  --qbf_dom_pre_inst                      false
% 2.94/0.98  --qbf_sk_in                             false
% 2.94/0.98  --qbf_pred_elim                         true
% 2.94/0.98  --qbf_split                             512
% 2.94/0.98  
% 2.94/0.98  ------ BMC1 Options
% 2.94/0.98  
% 2.94/0.98  --bmc1_incremental                      false
% 2.94/0.98  --bmc1_axioms                           reachable_all
% 2.94/0.98  --bmc1_min_bound                        0
% 2.94/0.98  --bmc1_max_bound                        -1
% 2.94/0.98  --bmc1_max_bound_default                -1
% 2.94/0.98  --bmc1_symbol_reachability              true
% 2.94/0.98  --bmc1_property_lemmas                  false
% 2.94/0.98  --bmc1_k_induction                      false
% 2.94/0.98  --bmc1_non_equiv_states                 false
% 2.94/0.98  --bmc1_deadlock                         false
% 2.94/0.98  --bmc1_ucm                              false
% 2.94/0.98  --bmc1_add_unsat_core                   none
% 2.94/0.98  --bmc1_unsat_core_children              false
% 2.94/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.98  --bmc1_out_stat                         full
% 2.94/0.98  --bmc1_ground_init                      false
% 2.94/0.98  --bmc1_pre_inst_next_state              false
% 2.94/0.98  --bmc1_pre_inst_state                   false
% 2.94/0.98  --bmc1_pre_inst_reach_state             false
% 2.94/0.98  --bmc1_out_unsat_core                   false
% 2.94/0.98  --bmc1_aig_witness_out                  false
% 2.94/0.98  --bmc1_verbose                          false
% 2.94/0.98  --bmc1_dump_clauses_tptp                false
% 2.94/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.98  --bmc1_dump_file                        -
% 2.94/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.98  --bmc1_ucm_extend_mode                  1
% 2.94/0.98  --bmc1_ucm_init_mode                    2
% 2.94/0.98  --bmc1_ucm_cone_mode                    none
% 2.94/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.98  --bmc1_ucm_relax_model                  4
% 2.94/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.98  --bmc1_ucm_layered_model                none
% 2.94/0.98  --bmc1_ucm_max_lemma_size               10
% 2.94/0.98  
% 2.94/0.98  ------ AIG Options
% 2.94/0.98  
% 2.94/0.98  --aig_mode                              false
% 2.94/0.98  
% 2.94/0.98  ------ Instantiation Options
% 2.94/0.98  
% 2.94/0.98  --instantiation_flag                    true
% 2.94/0.98  --inst_sos_flag                         false
% 2.94/0.98  --inst_sos_phase                        true
% 2.94/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.98  --inst_lit_sel_side                     num_symb
% 2.94/0.98  --inst_solver_per_active                1400
% 2.94/0.98  --inst_solver_calls_frac                1.
% 2.94/0.98  --inst_passive_queue_type               priority_queues
% 2.94/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.98  --inst_passive_queues_freq              [25;2]
% 2.94/0.98  --inst_dismatching                      true
% 2.94/0.98  --inst_eager_unprocessed_to_passive     true
% 2.94/0.98  --inst_prop_sim_given                   true
% 2.94/0.98  --inst_prop_sim_new                     false
% 2.94/0.98  --inst_subs_new                         false
% 2.94/0.98  --inst_eq_res_simp                      false
% 2.94/0.98  --inst_subs_given                       false
% 2.94/0.98  --inst_orphan_elimination               true
% 2.94/0.98  --inst_learning_loop_flag               true
% 2.94/0.98  --inst_learning_start                   3000
% 2.94/0.98  --inst_learning_factor                  2
% 2.94/0.98  --inst_start_prop_sim_after_learn       3
% 2.94/0.98  --inst_sel_renew                        solver
% 2.94/0.98  --inst_lit_activity_flag                true
% 2.94/0.98  --inst_restr_to_given                   false
% 2.94/0.98  --inst_activity_threshold               500
% 2.94/0.98  --inst_out_proof                        true
% 2.94/0.98  
% 2.94/0.98  ------ Resolution Options
% 2.94/0.98  
% 2.94/0.98  --resolution_flag                       true
% 2.94/0.98  --res_lit_sel                           adaptive
% 2.94/0.98  --res_lit_sel_side                      none
% 2.94/0.98  --res_ordering                          kbo
% 2.94/0.98  --res_to_prop_solver                    active
% 2.94/0.98  --res_prop_simpl_new                    false
% 2.94/0.98  --res_prop_simpl_given                  true
% 2.94/0.98  --res_passive_queue_type                priority_queues
% 2.94/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.98  --res_passive_queues_freq               [15;5]
% 2.94/0.98  --res_forward_subs                      full
% 2.94/0.98  --res_backward_subs                     full
% 2.94/0.98  --res_forward_subs_resolution           true
% 2.94/0.98  --res_backward_subs_resolution          true
% 2.94/0.98  --res_orphan_elimination                true
% 2.94/0.98  --res_time_limit                        2.
% 2.94/0.98  --res_out_proof                         true
% 2.94/0.98  
% 2.94/0.98  ------ Superposition Options
% 2.94/0.98  
% 2.94/0.98  --superposition_flag                    true
% 2.94/0.98  --sup_passive_queue_type                priority_queues
% 2.94/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.98  --demod_completeness_check              fast
% 2.94/0.98  --demod_use_ground                      true
% 2.94/0.98  --sup_to_prop_solver                    passive
% 2.94/0.98  --sup_prop_simpl_new                    true
% 2.94/0.98  --sup_prop_simpl_given                  true
% 2.94/0.98  --sup_fun_splitting                     false
% 2.94/0.98  --sup_smt_interval                      50000
% 2.94/0.98  
% 2.94/0.98  ------ Superposition Simplification Setup
% 2.94/0.98  
% 2.94/0.98  --sup_indices_passive                   []
% 2.94/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.98  --sup_full_bw                           [BwDemod]
% 2.94/0.98  --sup_immed_triv                        [TrivRules]
% 2.94/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.98  --sup_immed_bw_main                     []
% 2.94/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.98  
% 2.94/0.98  ------ Combination Options
% 2.94/0.98  
% 2.94/0.98  --comb_res_mult                         3
% 2.94/0.98  --comb_sup_mult                         2
% 2.94/0.98  --comb_inst_mult                        10
% 2.94/0.98  
% 2.94/0.98  ------ Debug Options
% 2.94/0.98  
% 2.94/0.98  --dbg_backtrace                         false
% 2.94/0.98  --dbg_dump_prop_clauses                 false
% 2.94/0.98  --dbg_dump_prop_clauses_file            -
% 2.94/0.98  --dbg_out_stat                          false
% 2.94/0.98  ------ Parsing...
% 2.94/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/0.98  
% 2.94/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.94/0.98  
% 2.94/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/0.98  
% 2.94/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/0.98  ------ Proving...
% 2.94/0.98  ------ Problem Properties 
% 2.94/0.98  
% 2.94/0.98  
% 2.94/0.98  clauses                                 27
% 2.94/0.98  conjectures                             5
% 2.94/0.98  EPR                                     1
% 2.94/0.98  Horn                                    21
% 2.94/0.98  unary                                   7
% 2.94/0.98  binary                                  6
% 2.94/0.98  lits                                    74
% 2.94/0.98  lits eq                                 31
% 2.94/0.98  fd_pure                                 0
% 2.94/0.98  fd_pseudo                               0
% 2.94/0.98  fd_cond                                 5
% 2.94/0.98  fd_pseudo_cond                          0
% 2.94/0.98  AC symbols                              0
% 2.94/0.98  
% 2.94/0.98  ------ Schedule dynamic 5 is on 
% 2.94/0.98  
% 2.94/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/0.98  
% 2.94/0.98  
% 2.94/0.98  ------ 
% 2.94/0.98  Current options:
% 2.94/0.98  ------ 
% 2.94/0.98  
% 2.94/0.98  ------ Input Options
% 2.94/0.98  
% 2.94/0.98  --out_options                           all
% 2.94/0.98  --tptp_safe_out                         true
% 2.94/0.98  --problem_path                          ""
% 2.94/0.98  --include_path                          ""
% 2.94/0.98  --clausifier                            res/vclausify_rel
% 2.94/0.98  --clausifier_options                    --mode clausify
% 2.94/0.98  --stdin                                 false
% 2.94/0.98  --stats_out                             all
% 2.94/0.98  
% 2.94/0.98  ------ General Options
% 2.94/0.98  
% 2.94/0.98  --fof                                   false
% 2.94/0.98  --time_out_real                         305.
% 2.94/0.98  --time_out_virtual                      -1.
% 2.94/0.98  --symbol_type_check                     false
% 2.94/0.98  --clausify_out                          false
% 2.94/0.98  --sig_cnt_out                           false
% 2.94/0.98  --trig_cnt_out                          false
% 2.94/0.98  --trig_cnt_out_tolerance                1.
% 2.94/0.98  --trig_cnt_out_sk_spl                   false
% 2.94/0.98  --abstr_cl_out                          false
% 2.94/0.98  
% 2.94/0.98  ------ Global Options
% 2.94/0.98  
% 2.94/0.98  --schedule                              default
% 2.94/0.98  --add_important_lit                     false
% 2.94/0.98  --prop_solver_per_cl                    1000
% 2.94/0.98  --min_unsat_core                        false
% 2.94/0.98  --soft_assumptions                      false
% 2.94/0.98  --soft_lemma_size                       3
% 2.94/0.98  --prop_impl_unit_size                   0
% 2.94/0.98  --prop_impl_unit                        []
% 2.94/0.98  --share_sel_clauses                     true
% 2.94/0.98  --reset_solvers                         false
% 2.94/0.98  --bc_imp_inh                            [conj_cone]
% 2.94/0.98  --conj_cone_tolerance                   3.
% 2.94/0.98  --extra_neg_conj                        none
% 2.94/0.98  --large_theory_mode                     true
% 2.94/0.98  --prolific_symb_bound                   200
% 2.94/0.98  --lt_threshold                          2000
% 2.94/0.98  --clause_weak_htbl                      true
% 2.94/0.98  --gc_record_bc_elim                     false
% 2.94/0.98  
% 2.94/0.98  ------ Preprocessing Options
% 2.94/0.98  
% 2.94/0.98  --preprocessing_flag                    true
% 2.94/0.98  --time_out_prep_mult                    0.1
% 2.94/0.98  --splitting_mode                        input
% 2.94/0.98  --splitting_grd                         true
% 2.94/0.98  --splitting_cvd                         false
% 2.94/0.98  --splitting_cvd_svl                     false
% 2.94/0.98  --splitting_nvd                         32
% 2.94/0.98  --sub_typing                            true
% 2.94/0.98  --prep_gs_sim                           true
% 2.94/0.98  --prep_unflatten                        true
% 2.94/0.98  --prep_res_sim                          true
% 2.94/0.98  --prep_upred                            true
% 2.94/0.98  --prep_sem_filter                       exhaustive
% 2.94/0.98  --prep_sem_filter_out                   false
% 2.94/0.98  --pred_elim                             true
% 2.94/0.98  --res_sim_input                         true
% 2.94/0.98  --eq_ax_congr_red                       true
% 2.94/0.98  --pure_diseq_elim                       true
% 2.94/0.98  --brand_transform                       false
% 2.94/0.98  --non_eq_to_eq                          false
% 2.94/0.98  --prep_def_merge                        true
% 2.94/0.98  --prep_def_merge_prop_impl              false
% 2.94/0.98  --prep_def_merge_mbd                    true
% 2.94/0.98  --prep_def_merge_tr_red                 false
% 2.94/0.98  --prep_def_merge_tr_cl                  false
% 2.94/0.98  --smt_preprocessing                     true
% 2.94/0.98  --smt_ac_axioms                         fast
% 2.94/0.98  --preprocessed_out                      false
% 2.94/0.98  --preprocessed_stats                    false
% 2.94/0.98  
% 2.94/0.98  ------ Abstraction refinement Options
% 2.94/0.98  
% 2.94/0.98  --abstr_ref                             []
% 2.94/0.98  --abstr_ref_prep                        false
% 2.94/0.98  --abstr_ref_until_sat                   false
% 2.94/0.98  --abstr_ref_sig_restrict                funpre
% 2.94/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.98  --abstr_ref_under                       []
% 2.94/0.98  
% 2.94/0.98  ------ SAT Options
% 2.94/0.98  
% 2.94/0.98  --sat_mode                              false
% 2.94/0.98  --sat_fm_restart_options                ""
% 2.94/0.98  --sat_gr_def                            false
% 2.94/0.98  --sat_epr_types                         true
% 2.94/0.98  --sat_non_cyclic_types                  false
% 2.94/0.98  --sat_finite_models                     false
% 2.94/0.98  --sat_fm_lemmas                         false
% 2.94/0.98  --sat_fm_prep                           false
% 2.94/0.98  --sat_fm_uc_incr                        true
% 2.94/0.98  --sat_out_model                         small
% 2.94/0.98  --sat_out_clauses                       false
% 2.94/0.98  
% 2.94/0.98  ------ QBF Options
% 2.94/0.98  
% 2.94/0.98  --qbf_mode                              false
% 2.94/0.98  --qbf_elim_univ                         false
% 2.94/0.98  --qbf_dom_inst                          none
% 2.94/0.98  --qbf_dom_pre_inst                      false
% 2.94/0.98  --qbf_sk_in                             false
% 2.94/0.98  --qbf_pred_elim                         true
% 2.94/0.98  --qbf_split                             512
% 2.94/0.98  
% 2.94/0.98  ------ BMC1 Options
% 2.94/0.98  
% 2.94/0.98  --bmc1_incremental                      false
% 2.94/0.98  --bmc1_axioms                           reachable_all
% 2.94/0.98  --bmc1_min_bound                        0
% 2.94/0.98  --bmc1_max_bound                        -1
% 2.94/0.98  --bmc1_max_bound_default                -1
% 2.94/0.98  --bmc1_symbol_reachability              true
% 2.94/0.98  --bmc1_property_lemmas                  false
% 2.94/0.98  --bmc1_k_induction                      false
% 2.94/0.98  --bmc1_non_equiv_states                 false
% 2.94/0.98  --bmc1_deadlock                         false
% 2.94/0.98  --bmc1_ucm                              false
% 2.94/0.98  --bmc1_add_unsat_core                   none
% 2.94/0.98  --bmc1_unsat_core_children              false
% 2.94/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.98  --bmc1_out_stat                         full
% 2.94/0.98  --bmc1_ground_init                      false
% 2.94/0.98  --bmc1_pre_inst_next_state              false
% 2.94/0.98  --bmc1_pre_inst_state                   false
% 2.94/0.98  --bmc1_pre_inst_reach_state             false
% 2.94/0.98  --bmc1_out_unsat_core                   false
% 2.94/0.98  --bmc1_aig_witness_out                  false
% 2.94/0.98  --bmc1_verbose                          false
% 2.94/0.98  --bmc1_dump_clauses_tptp                false
% 2.94/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.98  --bmc1_dump_file                        -
% 2.94/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.98  --bmc1_ucm_extend_mode                  1
% 2.94/0.98  --bmc1_ucm_init_mode                    2
% 2.94/0.98  --bmc1_ucm_cone_mode                    none
% 2.94/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.98  --bmc1_ucm_relax_model                  4
% 2.94/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.98  --bmc1_ucm_layered_model                none
% 2.94/0.98  --bmc1_ucm_max_lemma_size               10
% 2.94/0.98  
% 2.94/0.98  ------ AIG Options
% 2.94/0.98  
% 2.94/0.98  --aig_mode                              false
% 2.94/0.98  
% 2.94/0.98  ------ Instantiation Options
% 2.94/0.98  
% 2.94/0.98  --instantiation_flag                    true
% 2.94/0.98  --inst_sos_flag                         false
% 2.94/0.98  --inst_sos_phase                        true
% 2.94/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.98  --inst_lit_sel_side                     none
% 2.94/0.98  --inst_solver_per_active                1400
% 2.94/0.98  --inst_solver_calls_frac                1.
% 2.94/0.98  --inst_passive_queue_type               priority_queues
% 2.94/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.98  --inst_passive_queues_freq              [25;2]
% 2.94/0.98  --inst_dismatching                      true
% 2.94/0.98  --inst_eager_unprocessed_to_passive     true
% 2.94/0.98  --inst_prop_sim_given                   true
% 2.94/0.98  --inst_prop_sim_new                     false
% 2.94/0.98  --inst_subs_new                         false
% 2.94/0.98  --inst_eq_res_simp                      false
% 2.94/0.98  --inst_subs_given                       false
% 2.94/0.98  --inst_orphan_elimination               true
% 2.94/0.98  --inst_learning_loop_flag               true
% 2.94/0.98  --inst_learning_start                   3000
% 2.94/0.98  --inst_learning_factor                  2
% 2.94/0.98  --inst_start_prop_sim_after_learn       3
% 2.94/0.98  --inst_sel_renew                        solver
% 2.94/0.98  --inst_lit_activity_flag                true
% 2.94/0.98  --inst_restr_to_given                   false
% 2.94/0.98  --inst_activity_threshold               500
% 2.94/0.98  --inst_out_proof                        true
% 2.94/0.98  
% 2.94/0.98  ------ Resolution Options
% 2.94/0.98  
% 2.94/0.98  --resolution_flag                       false
% 2.94/0.98  --res_lit_sel                           adaptive
% 2.94/0.98  --res_lit_sel_side                      none
% 2.94/0.98  --res_ordering                          kbo
% 2.94/0.98  --res_to_prop_solver                    active
% 2.94/0.98  --res_prop_simpl_new                    false
% 2.94/0.98  --res_prop_simpl_given                  true
% 2.94/0.98  --res_passive_queue_type                priority_queues
% 2.94/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.98  --res_passive_queues_freq               [15;5]
% 2.94/0.98  --res_forward_subs                      full
% 2.94/0.98  --res_backward_subs                     full
% 2.94/0.98  --res_forward_subs_resolution           true
% 2.94/0.98  --res_backward_subs_resolution          true
% 2.94/0.98  --res_orphan_elimination                true
% 2.94/0.98  --res_time_limit                        2.
% 2.94/0.98  --res_out_proof                         true
% 2.94/0.98  
% 2.94/0.98  ------ Superposition Options
% 2.94/0.98  
% 2.94/0.98  --superposition_flag                    true
% 2.94/0.98  --sup_passive_queue_type                priority_queues
% 2.94/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.98  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ Proving...
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS status Theorem for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99   Resolution empty clause
% 2.94/0.99  
% 2.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  fof(f13,conjecture,(
% 2.94/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f14,negated_conjecture,(
% 2.94/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.94/0.99    inference(negated_conjecture,[],[f13])).
% 2.94/0.99  
% 2.94/0.99  fof(f32,plain,(
% 2.94/0.99    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f14])).
% 2.94/0.99  
% 2.94/0.99  fof(f33,plain,(
% 2.94/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.94/0.99    inference(flattening,[],[f32])).
% 2.94/0.99  
% 2.94/0.99  fof(f37,plain,(
% 2.94/0.99    ( ! [X0,X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2))) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f36,plain,(
% 2.94/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f35,plain,(
% 2.94/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f38,plain,(
% 2.94/0.99    (((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).
% 2.94/0.99  
% 2.94/0.99  fof(f66,plain,(
% 2.94/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f11,axiom,(
% 2.94/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f29,plain,(
% 2.94/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f11])).
% 2.94/0.99  
% 2.94/0.99  fof(f59,plain,(
% 2.94/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f29])).
% 2.94/0.99  
% 2.94/0.99  fof(f62,plain,(
% 2.94/0.99    l1_struct_0(sK1)),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f61,plain,(
% 2.94/0.99    l1_struct_0(sK0)),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f9,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f25,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f9])).
% 2.94/0.99  
% 2.94/0.99  fof(f26,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f25])).
% 2.94/0.99  
% 2.94/0.99  fof(f56,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f26])).
% 2.94/0.99  
% 2.94/0.99  fof(f67,plain,(
% 2.94/0.99    v2_funct_1(sK2)),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f63,plain,(
% 2.94/0.99    v1_funct_1(sK2)),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f65,plain,(
% 2.94/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f64,plain,(
% 2.94/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f6,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f21,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f6])).
% 2.94/0.99  
% 2.94/0.99  fof(f22,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(flattening,[],[f21])).
% 2.94/0.99  
% 2.94/0.99  fof(f34,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f22])).
% 2.94/0.99  
% 2.94/0.99  fof(f46,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f34])).
% 2.94/0.99  
% 2.94/0.99  fof(f5,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f20,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f5])).
% 2.94/0.99  
% 2.94/0.99  fof(f45,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f20])).
% 2.94/0.99  
% 2.94/0.99  fof(f55,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f26])).
% 2.94/0.99  
% 2.94/0.99  fof(f1,axiom,(
% 2.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f15,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f1])).
% 2.94/0.99  
% 2.94/0.99  fof(f39,plain,(
% 2.94/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f15])).
% 2.94/0.99  
% 2.94/0.99  fof(f2,axiom,(
% 2.94/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f40,plain,(
% 2.94/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f2])).
% 2.94/0.99  
% 2.94/0.99  fof(f3,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f16,plain,(
% 2.94/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f3])).
% 2.94/0.99  
% 2.94/0.99  fof(f17,plain,(
% 2.94/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f16])).
% 2.94/0.99  
% 2.94/0.99  fof(f41,plain,(
% 2.94/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f17])).
% 2.94/0.99  
% 2.94/0.99  fof(f10,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f27,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f10])).
% 2.94/0.99  
% 2.94/0.99  fof(f28,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f27])).
% 2.94/0.99  
% 2.94/0.99  fof(f58,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f28])).
% 2.94/0.99  
% 2.94/0.99  fof(f4,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f18,plain,(
% 2.94/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f4])).
% 2.94/0.99  
% 2.94/0.99  fof(f19,plain,(
% 2.94/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f18])).
% 2.94/0.99  
% 2.94/0.99  fof(f44,plain,(
% 2.94/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f19])).
% 2.94/0.99  
% 2.94/0.99  fof(f8,axiom,(
% 2.94/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f53,plain,(
% 2.94/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f8])).
% 2.94/0.99  
% 2.94/0.99  fof(f69,plain,(
% 2.94/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(definition_unfolding,[],[f44,f53])).
% 2.94/0.99  
% 2.94/0.99  fof(f7,axiom,(
% 2.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f23,plain,(
% 2.94/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.94/0.99    inference(ennf_transformation,[],[f7])).
% 2.94/0.99  
% 2.94/0.99  fof(f24,plain,(
% 2.94/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.94/0.99    inference(flattening,[],[f23])).
% 2.94/0.99  
% 2.94/0.99  fof(f52,plain,(
% 2.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f24])).
% 2.94/0.99  
% 2.94/0.99  fof(f54,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f26])).
% 2.94/0.99  
% 2.94/0.99  fof(f12,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f30,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f12])).
% 2.94/0.99  
% 2.94/0.99  fof(f31,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f30])).
% 2.94/0.99  
% 2.94/0.99  fof(f60,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f31])).
% 2.94/0.99  
% 2.94/0.99  fof(f68,plain,(
% 2.94/0.99    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f43,plain,(
% 2.94/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f19])).
% 2.94/0.99  
% 2.94/0.99  fof(f70,plain,(
% 2.94/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(definition_unfolding,[],[f43,f53])).
% 2.94/0.99  
% 2.94/0.99  fof(f47,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f34])).
% 2.94/0.99  
% 2.94/0.99  fof(f75,plain,(
% 2.94/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.94/0.99    inference(equality_resolution,[],[f47])).
% 2.94/0.99  
% 2.94/0.99  cnf(c_23,negated_conjecture,
% 2.94/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_19,plain,
% 2.94/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_27,negated_conjecture,
% 2.94/0.99      ( l1_struct_0(sK1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_308,plain,
% 2.94/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_309,plain,
% 2.94/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_28,negated_conjecture,
% 2.94/0.99      ( l1_struct_0(sK0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_313,plain,
% 2.94/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_314,plain,
% 2.94/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1190,plain,
% 2.94/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_23,c_309,c_314]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_14,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_22,negated_conjecture,
% 2.94/0.99      ( v2_funct_1(sK2) ),
% 2.94/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_446,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_447,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_26,negated_conjecture,
% 2.94/0.99      ( v1_funct_1(sK2) ),
% 2.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_451,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_447,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_452,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_451]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1160,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1890,plain,
% 2.94/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1190,c_1160]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_24,negated_conjecture,
% 2.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1168,plain,
% 2.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1193,plain,
% 2.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_1168,c_309,c_314]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_25,negated_conjecture,
% 2.94/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1167,plain,
% 2.94/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1187,plain,
% 2.94/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_1167,c_309,c_314]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2261,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1890,c_1193,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_12,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1170,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.94/0.99      | k1_xboole_0 = X1
% 2.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2267,plain,
% 2.94/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.94/0.99      | k2_struct_0(sK0) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2261,c_1170]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1176,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2268,plain,
% 2.94/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2261,c_1176]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2271,plain,
% 2.94/0.99      ( k2_struct_0(sK0) = k1_xboole_0
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_2267,c_2268]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_15,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_422,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_423,plain,
% 2.94/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | ~ v1_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_427,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_423,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_428,plain,
% 2.94/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_427]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1161,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 2.94/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1764,plain,
% 2.94/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.94/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1190,c_1161]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3861,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.94/0.99      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2271,c_1193,c_1187,c_1764]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3862,plain,
% 2.94/0.99      ( k2_struct_0(sK0) = k1_xboole_0
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1) ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3861]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_0,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1178,plain,
% 2.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.94/0.99      | v1_relat_1(X1) != iProver_top
% 2.94/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1559,plain,
% 2.94/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.94/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1193,c_1178]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_33,plain,
% 2.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1398,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | v1_relat_1(X0)
% 2.94/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1473,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.94/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.94/0.99      | v1_relat_1(sK2) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1398]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1474,plain,
% 2.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.94/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.94/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1,plain,
% 2.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1561,plain,
% 2.94/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1562,plain,
% 2.94/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2572,plain,
% 2.94/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1559,c_33,c_1474,c_1562]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_498,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_499,plain,
% 2.94/0.99      ( ~ v1_funct_1(sK2)
% 2.94/0.99      | ~ v1_relat_1(sK2)
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_501,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_499,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1157,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.94/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2577,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2572,c_1157]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3863,plain,
% 2.94/0.99      ( k2_struct_0(sK0) = k1_xboole_0 | k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3862,c_2577]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3876,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2)
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3863,c_2261]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2174,plain,
% 2.94/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 2.94/0.99      | k2_struct_0(sK1) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1193,c_1170]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3122,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.94/0.99      | k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2174,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3123,plain,
% 2.94/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 2.94/0.99      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3122]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1554,plain,
% 2.94/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1193,c_1176]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3124,plain,
% 2.94/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3123,c_1554]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3133,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3124,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_31,plain,
% 2.94/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_17,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_371,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.94/0.99      | sK2 != X0
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_372,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.94/0.99      | k1_xboole_0 = X1 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_376,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.94/0.99      | k1_xboole_0 = X1 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_372,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_377,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.94/0.99      | k1_xboole_0 = X1 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_376]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1163,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.94/0.99      | k1_xboole_0 = X1
% 2.94/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_484,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_485,plain,
% 2.94/0.99      ( ~ v1_funct_1(sK2)
% 2.94/0.99      | ~ v1_relat_1(sK2)
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_487,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK2)
% 2.94/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_485,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1158,plain,
% 2.94/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.94/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1614,plain,
% 2.94/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1158,c_26,c_24,c_485,c_1473,c_1561]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1893,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(X1)
% 2.94/0.99      | k1_xboole_0 = X1
% 2.94/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_1163,c_1614]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1900,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.94/0.99      | k6_partfun1(k2_struct_0(sK1)) = k6_partfun1(k2_relat_1(sK2))
% 2.94/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1190,c_1893]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2374,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.94/0.99      | k6_partfun1(k2_struct_0(sK1)) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1900,c_1193,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_13,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X3)
% 2.94/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1169,plain,
% 2.94/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.94/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.94/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | v1_funct_1(X5) != iProver_top
% 2.94/0.99      | v1_funct_1(X4) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2883,plain,
% 2.94/0.99      ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | v1_funct_1(X2) != iProver_top
% 2.94/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1193,c_1169]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3524,plain,
% 2.94/0.99      ( v1_funct_1(X2) != iProver_top
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2883,c_31]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3525,plain,
% 2.94/0.99      ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3524]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3534,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2261,c_3525]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3537,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3534,c_1614]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_32,plain,
% 2.94/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_16,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_398,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_399,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2))
% 2.94/0.99      | ~ v1_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_403,plain,
% 2.94/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_399,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_404,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2))
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_403]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1384,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2))
% 2.94/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_404]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1385,plain,
% 2.94/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.94/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_735,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1442,plain,
% 2.94/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 2.94/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.94/0.99      | u1_struct_0(sK1) != X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_735]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1589,plain,
% 2.94/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.94/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.94/0.99      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1442]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3744,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3537,c_32,c_33,c_23,c_309,c_1385,c_1589]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_20,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_320,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.94/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_321,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_1(sK2)
% 2.94/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_325,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_321,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_326,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_325]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1165,plain,
% 2.94/0.99      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.94/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1825,plain,
% 2.94/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.94/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1190,c_1165]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1828,plain,
% 2.94/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1825,c_1193,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_21,negated_conjecture,
% 2.94/0.99      ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.94/0.99      | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1326,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
% 2.94/0.99      | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_21,c_309,c_314,c_1190]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1831,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
% 2.94/0.99      | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_1828,c_1326]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2472,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 2.94/0.99      | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) != k6_partfun1(k2_struct_0(sK1)) ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_1554,c_1831]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3747,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 2.94/0.99      | k6_partfun1(k2_struct_0(sK1)) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_3744,c_2472]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2884,plain,
% 2.94/0.99      ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | v1_funct_1(X2) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2261,c_1169]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3751,plain,
% 2.94/0.99      ( v1_funct_1(X2) != iProver_top
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2884,c_32,c_33,c_23,c_309,c_1385,c_1589]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3752,plain,
% 2.94/0.99      ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.94/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3751]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3760,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.94/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1193,c_3752]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v2_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_470,plain,
% 2.94/0.99      ( ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.94/0.99      | sK2 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_471,plain,
% 2.94/0.99      ( ~ v1_funct_1(sK2)
% 2.94/0.99      | ~ v1_relat_1(sK2)
% 2.94/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_473,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK2)
% 2.94/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_471,c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1159,plain,
% 2.94/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.94/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1659,plain,
% 2.94/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1159,c_26,c_24,c_471,c_1473,c_1561]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3768,plain,
% 2.94/0.99      ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.94/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3760,c_1659]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4150,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3133,c_31,c_2374,c_3747,c_3768]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5374,plain,
% 2.94/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3876,c_4150]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5381,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
% 2.94/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_5374,c_1176]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5403,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.94/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_5381,c_2577]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_11,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1171,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 2.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5383,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
% 2.94/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_5374,c_1171]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1767,plain,
% 2.94/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1764,c_1193,c_1187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3878,plain,
% 2.94/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2)
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3863,c_1767]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5082,plain,
% 2.94/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 2.94/0.99      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3878,c_4150]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5503,plain,
% 2.94/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 2.94/0.99      | k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5383,c_5082]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5504,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
% 2.94/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_5503]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5828,plain,
% 2.94/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_5403,c_5504]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6551,plain,
% 2.94/0.99      ( k6_partfun1(k2_struct_0(sK1)) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3747,c_31,c_3768]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6553,plain,
% 2.94/0.99      ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_xboole_0) ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_6551,c_4150]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6650,plain,
% 2.94/0.99      ( k6_partfun1(k1_xboole_0) != k6_partfun1(k1_xboole_0) ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_5828,c_6553]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6675,plain,
% 2.94/0.99      ( $false ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_6650]) ).
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  ------                               Statistics
% 2.94/0.99  
% 2.94/0.99  ------ General
% 2.94/0.99  
% 2.94/0.99  abstr_ref_over_cycles:                  0
% 2.94/0.99  abstr_ref_under_cycles:                 0
% 2.94/0.99  gc_basic_clause_elim:                   0
% 2.94/0.99  forced_gc_time:                         0
% 2.94/0.99  parsing_time:                           0.011
% 2.94/0.99  unif_index_cands_time:                  0.
% 2.94/0.99  unif_index_add_time:                    0.
% 2.94/0.99  orderings_time:                         0.
% 2.94/0.99  out_proof_time:                         0.013
% 2.94/0.99  total_time:                             0.223
% 2.94/0.99  num_of_symbols:                         54
% 2.94/0.99  num_of_terms:                           5683
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing
% 2.94/0.99  
% 2.94/0.99  num_of_splits:                          0
% 2.94/0.99  num_of_split_atoms:                     0
% 2.94/0.99  num_of_reused_defs:                     0
% 2.94/0.99  num_eq_ax_congr_red:                    1
% 2.94/0.99  num_of_sem_filtered_clauses:            1
% 2.94/0.99  num_of_subtypes:                        0
% 2.94/0.99  monotx_restored_types:                  0
% 2.94/0.99  sat_num_of_epr_types:                   0
% 2.94/0.99  sat_num_of_non_cyclic_types:            0
% 2.94/0.99  sat_guarded_non_collapsed_types:        0
% 2.94/0.99  num_pure_diseq_elim:                    0
% 2.94/0.99  simp_replaced_by:                       0
% 2.94/0.99  res_preprocessed:                       149
% 2.94/0.99  prep_upred:                             0
% 2.94/0.99  prep_unflattend:                        12
% 2.94/0.99  smt_new_axioms:                         0
% 2.94/0.99  pred_elim_cands:                        4
% 2.94/0.99  pred_elim:                              2
% 2.94/0.99  pred_elim_cl:                           2
% 2.94/0.99  pred_elim_cycles:                       4
% 2.94/0.99  merged_defs:                            0
% 2.94/0.99  merged_defs_ncl:                        0
% 2.94/0.99  bin_hyper_res:                          0
% 2.94/0.99  prep_cycles:                            4
% 2.94/0.99  pred_elim_time:                         0.007
% 2.94/0.99  splitting_time:                         0.
% 2.94/0.99  sem_filter_time:                        0.
% 2.94/0.99  monotx_time:                            0.001
% 2.94/0.99  subtype_inf_time:                       0.
% 2.94/0.99  
% 2.94/0.99  ------ Problem properties
% 2.94/0.99  
% 2.94/0.99  clauses:                                27
% 2.94/0.99  conjectures:                            5
% 2.94/0.99  epr:                                    1
% 2.94/0.99  horn:                                   21
% 2.94/0.99  ground:                                 11
% 2.94/0.99  unary:                                  7
% 2.94/0.99  binary:                                 6
% 2.94/0.99  lits:                                   74
% 2.94/0.99  lits_eq:                                31
% 2.94/0.99  fd_pure:                                0
% 2.94/0.99  fd_pseudo:                              0
% 2.94/0.99  fd_cond:                                5
% 2.94/0.99  fd_pseudo_cond:                         0
% 2.94/0.99  ac_symbols:                             0
% 2.94/0.99  
% 2.94/0.99  ------ Propositional Solver
% 2.94/0.99  
% 2.94/0.99  prop_solver_calls:                      29
% 2.94/0.99  prop_fast_solver_calls:                 1264
% 2.94/0.99  smt_solver_calls:                       0
% 2.94/0.99  smt_fast_solver_calls:                  0
% 2.94/0.99  prop_num_of_clauses:                    2103
% 2.94/0.99  prop_preprocess_simplified:             7131
% 2.94/0.99  prop_fo_subsumed:                       62
% 2.94/0.99  prop_solver_time:                       0.
% 2.94/0.99  smt_solver_time:                        0.
% 2.94/0.99  smt_fast_solver_time:                   0.
% 2.94/0.99  prop_fast_solver_time:                  0.
% 2.94/0.99  prop_unsat_core_time:                   0.
% 2.94/0.99  
% 2.94/0.99  ------ QBF
% 2.94/0.99  
% 2.94/0.99  qbf_q_res:                              0
% 2.94/0.99  qbf_num_tautologies:                    0
% 2.94/0.99  qbf_prep_cycles:                        0
% 2.94/0.99  
% 2.94/0.99  ------ BMC1
% 2.94/0.99  
% 2.94/0.99  bmc1_current_bound:                     -1
% 2.94/0.99  bmc1_last_solved_bound:                 -1
% 2.94/0.99  bmc1_unsat_core_size:                   -1
% 2.94/0.99  bmc1_unsat_core_parents_size:           -1
% 2.94/0.99  bmc1_merge_next_fun:                    0
% 2.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation
% 2.94/0.99  
% 2.94/0.99  inst_num_of_clauses:                    838
% 2.94/0.99  inst_num_in_passive:                    406
% 2.94/0.99  inst_num_in_active:                     388
% 2.94/0.99  inst_num_in_unprocessed:                44
% 2.94/0.99  inst_num_of_loops:                      420
% 2.94/0.99  inst_num_of_learning_restarts:          0
% 2.94/0.99  inst_num_moves_active_passive:          28
% 2.94/0.99  inst_lit_activity:                      0
% 2.94/0.99  inst_lit_activity_moves:                0
% 2.94/0.99  inst_num_tautologies:                   0
% 2.94/0.99  inst_num_prop_implied:                  0
% 2.94/0.99  inst_num_existing_simplified:           0
% 2.94/0.99  inst_num_eq_res_simplified:             0
% 2.94/0.99  inst_num_child_elim:                    0
% 2.94/0.99  inst_num_of_dismatching_blockings:      132
% 2.94/0.99  inst_num_of_non_proper_insts:           585
% 2.94/0.99  inst_num_of_duplicates:                 0
% 2.94/0.99  inst_inst_num_from_inst_to_res:         0
% 2.94/0.99  inst_dismatching_checking_time:         0.
% 2.94/0.99  
% 2.94/0.99  ------ Resolution
% 2.94/0.99  
% 2.94/0.99  res_num_of_clauses:                     0
% 2.94/0.99  res_num_in_passive:                     0
% 2.94/0.99  res_num_in_active:                      0
% 2.94/0.99  res_num_of_loops:                       153
% 2.94/0.99  res_forward_subset_subsumed:            58
% 2.94/0.99  res_backward_subset_subsumed:           4
% 2.94/0.99  res_forward_subsumed:                   0
% 2.94/0.99  res_backward_subsumed:                  0
% 2.94/0.99  res_forward_subsumption_resolution:     0
% 2.94/0.99  res_backward_subsumption_resolution:    0
% 2.94/0.99  res_clause_to_clause_subsumption:       143
% 2.94/0.99  res_orphan_elimination:                 0
% 2.94/0.99  res_tautology_del:                      66
% 2.94/0.99  res_num_eq_res_simplified:              0
% 2.94/0.99  res_num_sel_changes:                    0
% 2.94/0.99  res_moves_from_active_to_pass:          0
% 2.94/0.99  
% 2.94/0.99  ------ Superposition
% 2.94/0.99  
% 2.94/0.99  sup_time_total:                         0.
% 2.94/0.99  sup_time_generating:                    0.
% 2.94/0.99  sup_time_sim_full:                      0.
% 2.94/0.99  sup_time_sim_immed:                     0.
% 2.94/0.99  
% 2.94/0.99  sup_num_of_clauses:                     73
% 2.94/0.99  sup_num_in_active:                      43
% 2.94/0.99  sup_num_in_passive:                     30
% 2.94/0.99  sup_num_of_loops:                       82
% 2.94/0.99  sup_fw_superposition:                   63
% 2.94/0.99  sup_bw_superposition:                   99
% 2.94/0.99  sup_immediate_simplified:               51
% 2.94/0.99  sup_given_eliminated:                   1
% 2.94/0.99  comparisons_done:                       0
% 2.94/0.99  comparisons_avoided:                    30
% 2.94/0.99  
% 2.94/0.99  ------ Simplifications
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  sim_fw_subset_subsumed:                 41
% 2.94/0.99  sim_bw_subset_subsumed:                 14
% 2.94/0.99  sim_fw_subsumed:                        1
% 2.94/0.99  sim_bw_subsumed:                        0
% 2.94/0.99  sim_fw_subsumption_res:                 0
% 2.94/0.99  sim_bw_subsumption_res:                 0
% 2.94/0.99  sim_tautology_del:                      2
% 2.94/0.99  sim_eq_tautology_del:                   22
% 2.94/0.99  sim_eq_res_simp:                        0
% 2.94/0.99  sim_fw_demodulated:                     3
% 2.94/0.99  sim_bw_demodulated:                     31
% 2.94/0.99  sim_light_normalised:                   23
% 2.94/0.99  sim_joinable_taut:                      0
% 2.94/0.99  sim_joinable_simp:                      0
% 2.94/0.99  sim_ac_normalised:                      0
% 2.94/0.99  sim_smt_subsumption:                    0
% 2.94/0.99  
%------------------------------------------------------------------------------
