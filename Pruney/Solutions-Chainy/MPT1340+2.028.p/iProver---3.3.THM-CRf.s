%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:26 EST 2020

% Result     : Theorem 6.84s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  318 (2010055038 expanded)
%              Number of clauses        :  244 (518138925 expanded)
%              Number of leaves         :   21 (572348200 expanded)
%              Depth                    :   69
%              Number of atoms          : 1070 (12577620353 expanded)
%              Number of equality atoms :  662 (2319336933 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f42,f41,f40])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f76,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1078,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1075,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_369,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_370,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_374,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_375,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1075,c_370,c_375])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1089,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1579,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1112,c_1089])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1109,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_27,c_370,c_375])).

cnf(c_1751,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1579,c_1109])).

cnf(c_1755,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1751,c_1112])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1083,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3000,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1083])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1090,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1583,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1112,c_1090])).

cnf(c_1874,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1583,c_1751])).

cnf(c_3001,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3000,c_1874])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1074,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1106,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1074,c_370,c_375])).

cnf(c_1756,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1751,c_1106])).

cnf(c_3165,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3001,c_1756])).

cnf(c_3166,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3165])).

cnf(c_1753,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1751,c_1579])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1080,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3960,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_1080])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4171,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_35,c_38,c_1755,c_1756])).

cnf(c_15,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_384,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1071,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1285,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1071,c_370,c_375])).

cnf(c_1754,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1751,c_1285])).

cnf(c_4176,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4171,c_1754])).

cnf(c_4305,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_4176])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1438,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1442,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1438])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1081,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3993,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_1081])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1079,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4198,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4171,c_1079])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1082,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4139,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_1082])).

cnf(c_4441,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4198,c_35,c_38,c_1755,c_1756,c_4139])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1077,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4447,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_1077])).

cnf(c_4452,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4441,c_1089])).

cnf(c_1091,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1466,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1091])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1094,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2781,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1094])).

cnf(c_1435,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3102,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2781,c_30,c_28,c_26,c_1357,c_1435])).

cnf(c_4454,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4452,c_3102])).

cnf(c_4482,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4454,c_1080])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1092,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2127,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1092])).

cnf(c_1433,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2406,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2127,c_30,c_28,c_26,c_1357,c_1433])).

cnf(c_4489,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4482,c_2406])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1439,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1440,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1439])).

cnf(c_4945,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4489,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_1755,c_1756,c_3993,c_4139])).

cnf(c_4949,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3166,c_4945])).

cnf(c_4951,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,c_4176,c_4447,c_4949])).

cnf(c_4952,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4951])).

cnf(c_4959,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_4952])).

cnf(c_4958,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_4952])).

cnf(c_5150,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4959,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,c_4139,c_4958])).

cnf(c_5151,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5150])).

cnf(c_5157,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_5151])).

cnf(c_5156,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_5151])).

cnf(c_5174,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5157,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,c_4139,c_5156])).

cnf(c_5188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_1755])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1087,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5743,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5188,c_1087])).

cnf(c_5191,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_1756])).

cnf(c_5970,plain,
    ( sK2 = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5743,c_5191])).

cnf(c_5971,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5970])).

cnf(c_4708,plain,
    ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4447,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993])).

cnf(c_5178,plain,
    ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_4708])).

cnf(c_5183,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_4176])).

cnf(c_5228,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5178,c_5183])).

cnf(c_8780,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != sK2
    | sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_5228])).

cnf(c_5189,plain,
    ( k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5174,c_1753])).

cnf(c_5979,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5971,c_5189])).

cnf(c_6592,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5979,c_1082])).

cnf(c_5976,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_5188])).

cnf(c_5978,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_5191])).

cnf(c_7083,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6592,c_35,c_38,c_5976,c_5978])).

cnf(c_7084,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7083])).

cnf(c_7097,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7084,c_1089])).

cnf(c_7125,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7097,c_3102])).

cnf(c_7268,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7125,c_1080])).

cnf(c_7276,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
    | k1_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7268,c_2406])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1084,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6756,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5976,c_1084])).

cnf(c_6893,plain,
    ( sK2 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6756,c_5978])).

cnf(c_6894,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6893])).

cnf(c_5190,plain,
    ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5174,c_1874])).

cnf(c_5977,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5971,c_5190])).

cnf(c_6900,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6894,c_5977])).

cnf(c_6593,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5979,c_1081])).

cnf(c_7076,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6593,c_35,c_38,c_5976,c_5978])).

cnf(c_8013,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7276,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_6900,c_7076,c_7084])).

cnf(c_8792,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8780,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_6900,c_7076,c_7084,c_7276])).

cnf(c_8802,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_8792])).

cnf(c_5181,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_4441])).

cnf(c_4199,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4171,c_1078])).

cnf(c_4308,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4199,c_35,c_38,c_1755,c_1756,c_3993])).

cnf(c_5182,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5174,c_4308])).

cnf(c_8799,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_8792])).

cnf(c_8832,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8802,c_35,c_37,c_38,c_1358,c_1442,c_5181,c_5182,c_8799])).

cnf(c_8833,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8832])).

cnf(c_8841,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_8833])).

cnf(c_8838,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_8833])).

cnf(c_8858,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8841,c_35,c_37,c_38,c_1358,c_1442,c_5181,c_5182,c_8838])).

cnf(c_8877,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8858,c_5188])).

cnf(c_3770,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1087])).

cnf(c_7315,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3770,c_1078])).

cnf(c_7317,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_7315])).

cnf(c_12213,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7317,c_1077,c_1078])).

cnf(c_12216,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8877,c_12213])).

cnf(c_5184,plain,
    ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5174,c_4171])).

cnf(c_8875,plain,
    ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8858,c_5184])).

cnf(c_12221,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12216,c_8875])).

cnf(c_588,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_621,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_589,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1477,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_1478,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_592,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1503,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | X0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1807,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(X0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1810,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(k1_xboole_0))
    | k2_funct_1(k1_xboole_0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_590,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_1808,plain,
    ( X0 != sK2
    | k2_funct_1(X0) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_1813,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_8868,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8858,c_5182])).

cnf(c_8950,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8868])).

cnf(c_8865,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8858,c_5181])).

cnf(c_13271,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8865,c_7315])).

cnf(c_13328,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13271])).

cnf(c_17179,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12221,c_30,c_35,c_28,c_37,c_26,c_38,c_621,c_1357,c_1358,c_1438,c_1442,c_1478,c_1810,c_1813,c_5181,c_5182,c_8838,c_8950,c_13328])).

cnf(c_8861,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8858,c_5228])).

cnf(c_17201,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17179,c_8861])).

cnf(c_18504,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17179,c_17201])).

cnf(c_1809,plain,
    ( k2_funct_1(X0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_1811,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_18503,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_17201])).

cnf(c_18611,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18504,c_35,c_37,c_38,c_621,c_1358,c_1442,c_1478,c_1811,c_1813,c_5181,c_5182,c_8838,c_8865,c_8868,c_18503])).

cnf(c_18612,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18611])).

cnf(c_18617,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_18612])).

cnf(c_19128,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18617,c_35,c_37,c_38,c_621,c_1358,c_1442,c_1478,c_1811,c_1813,c_5181,c_5182,c_8838,c_8865,c_8868])).

cnf(c_19161,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19128,c_8877])).

cnf(c_3774,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1084])).

cnf(c_7488,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3774,c_1078])).

cnf(c_7492,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,k2_tops_2(k1_xboole_0,X0,X1))) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(k1_xboole_0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_7488])).

cnf(c_12042,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,k2_tops_2(k1_xboole_0,X0,X1))) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7492,c_1077,c_1078])).

cnf(c_19634,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19161,c_12042])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1365,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1366,plain,
    ( X0 != sK2
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_1368,plain,
    ( k1_xboole_0 != sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_2098,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_2099,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_2686,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1757,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1751,c_370])).

cnf(c_5192,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5174,c_1757])).

cnf(c_2689,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_6581,plain,
    ( X0 = u1_struct_0(sK0)
    | X0 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2689])).

cnf(c_6582,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_6581])).

cnf(c_601,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1413,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X2 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_7234,plain,
    ( v1_funct_2(X0,u1_struct_0(sK0),X1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X1 != u1_struct_0(sK1)
    | X0 != sK2
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_7235,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != sK2
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_funct_2(X1,u1_struct_0(sK0),X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7234])).

cnf(c_7237,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != sK2
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7235])).

cnf(c_7386,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_7387,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7386])).

cnf(c_7651,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK0),X4)
    | X0 != X3
    | X2 != X4
    | X1 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_7652,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != u1_struct_0(sK0)
    | v1_funct_2(X0,X4,X2) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7651])).

cnf(c_7654,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7652])).

cnf(c_12044,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12042])).

cnf(c_20333,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19634,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1368,c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_12044,c_18617,c_19161])).

cnf(c_19159,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_19128,c_8875])).

cnf(c_20335,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20333,c_19159])).

cnf(c_11,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1086,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20338,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20335,c_1086])).

cnf(c_19145,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19128,c_8861])).

cnf(c_5177,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5174,c_4945])).

cnf(c_8864,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8858,c_5177])).

cnf(c_19152,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19128,c_8864])).

cnf(c_19636,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19161,c_1084])).

cnf(c_8878,plain,
    ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8858,c_5190])).

cnf(c_19162,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_19128,c_8878])).

cnf(c_19655,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19636,c_19162])).

cnf(c_20719,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20338,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,c_19145,c_19152,c_19655])).

cnf(c_3773,plain,
    ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1089])).

cnf(c_19639,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19161,c_3773])).

cnf(c_1414,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X2 != sK2
    | v1_funct_2(X2,X1,X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1413])).

cnf(c_1416,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != sK2
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_3872,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3773])).

cnf(c_20345,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19639,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1368,c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_3872,c_5181,c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,c_19161])).

cnf(c_19773,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19655,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_18617])).

cnf(c_8884,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8858,c_3102])).

cnf(c_19777,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19773,c_8884])).

cnf(c_20347,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20345,c_19159,c_19777])).

cnf(c_20351,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k2_funct_1(k2_funct_1(k1_xboole_0))
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20347,c_1080])).

cnf(c_8885,plain,
    ( k2_funct_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8858,c_2406])).

cnf(c_20357,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20351,c_8885])).

cnf(c_20536,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20357,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,c_19152,c_19655])).

cnf(c_20723,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20719,c_20536])).

cnf(c_20725,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20723,c_19161])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.84/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.84/1.48  
% 6.84/1.48  ------  iProver source info
% 6.84/1.48  
% 6.84/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.84/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.84/1.48  git: non_committed_changes: false
% 6.84/1.48  git: last_make_outside_of_git: false
% 6.84/1.48  
% 6.84/1.48  ------ 
% 6.84/1.48  
% 6.84/1.48  ------ Input Options
% 6.84/1.48  
% 6.84/1.48  --out_options                           all
% 6.84/1.48  --tptp_safe_out                         true
% 6.84/1.48  --problem_path                          ""
% 6.84/1.48  --include_path                          ""
% 6.84/1.48  --clausifier                            res/vclausify_rel
% 6.84/1.48  --clausifier_options                    --mode clausify
% 6.84/1.48  --stdin                                 false
% 6.84/1.48  --stats_out                             all
% 6.84/1.48  
% 6.84/1.48  ------ General Options
% 6.84/1.48  
% 6.84/1.48  --fof                                   false
% 6.84/1.48  --time_out_real                         305.
% 6.84/1.48  --time_out_virtual                      -1.
% 6.84/1.48  --symbol_type_check                     false
% 6.84/1.48  --clausify_out                          false
% 6.84/1.48  --sig_cnt_out                           false
% 6.84/1.48  --trig_cnt_out                          false
% 6.84/1.48  --trig_cnt_out_tolerance                1.
% 6.84/1.48  --trig_cnt_out_sk_spl                   false
% 6.84/1.48  --abstr_cl_out                          false
% 6.84/1.48  
% 6.84/1.48  ------ Global Options
% 6.84/1.48  
% 6.84/1.48  --schedule                              default
% 6.84/1.48  --add_important_lit                     false
% 6.84/1.48  --prop_solver_per_cl                    1000
% 6.84/1.48  --min_unsat_core                        false
% 6.84/1.48  --soft_assumptions                      false
% 6.84/1.48  --soft_lemma_size                       3
% 6.84/1.48  --prop_impl_unit_size                   0
% 6.84/1.48  --prop_impl_unit                        []
% 6.84/1.48  --share_sel_clauses                     true
% 6.84/1.48  --reset_solvers                         false
% 6.84/1.48  --bc_imp_inh                            [conj_cone]
% 6.84/1.48  --conj_cone_tolerance                   3.
% 6.84/1.48  --extra_neg_conj                        none
% 6.84/1.48  --large_theory_mode                     true
% 6.84/1.48  --prolific_symb_bound                   200
% 6.84/1.48  --lt_threshold                          2000
% 6.84/1.48  --clause_weak_htbl                      true
% 6.84/1.48  --gc_record_bc_elim                     false
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing Options
% 6.84/1.48  
% 6.84/1.48  --preprocessing_flag                    true
% 6.84/1.48  --time_out_prep_mult                    0.1
% 6.84/1.48  --splitting_mode                        input
% 6.84/1.48  --splitting_grd                         true
% 6.84/1.48  --splitting_cvd                         false
% 6.84/1.48  --splitting_cvd_svl                     false
% 6.84/1.48  --splitting_nvd                         32
% 6.84/1.48  --sub_typing                            true
% 6.84/1.48  --prep_gs_sim                           true
% 6.84/1.48  --prep_unflatten                        true
% 6.84/1.48  --prep_res_sim                          true
% 6.84/1.48  --prep_upred                            true
% 6.84/1.48  --prep_sem_filter                       exhaustive
% 6.84/1.48  --prep_sem_filter_out                   false
% 6.84/1.48  --pred_elim                             true
% 6.84/1.48  --res_sim_input                         true
% 6.84/1.48  --eq_ax_congr_red                       true
% 6.84/1.48  --pure_diseq_elim                       true
% 6.84/1.48  --brand_transform                       false
% 6.84/1.48  --non_eq_to_eq                          false
% 6.84/1.48  --prep_def_merge                        true
% 6.84/1.48  --prep_def_merge_prop_impl              false
% 6.84/1.48  --prep_def_merge_mbd                    true
% 6.84/1.48  --prep_def_merge_tr_red                 false
% 6.84/1.48  --prep_def_merge_tr_cl                  false
% 6.84/1.48  --smt_preprocessing                     true
% 6.84/1.48  --smt_ac_axioms                         fast
% 6.84/1.48  --preprocessed_out                      false
% 6.84/1.48  --preprocessed_stats                    false
% 6.84/1.48  
% 6.84/1.48  ------ Abstraction refinement Options
% 6.84/1.48  
% 6.84/1.48  --abstr_ref                             []
% 6.84/1.48  --abstr_ref_prep                        false
% 6.84/1.48  --abstr_ref_until_sat                   false
% 6.84/1.48  --abstr_ref_sig_restrict                funpre
% 6.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.48  --abstr_ref_under                       []
% 6.84/1.48  
% 6.84/1.48  ------ SAT Options
% 6.84/1.48  
% 6.84/1.48  --sat_mode                              false
% 6.84/1.48  --sat_fm_restart_options                ""
% 6.84/1.48  --sat_gr_def                            false
% 6.84/1.48  --sat_epr_types                         true
% 6.84/1.48  --sat_non_cyclic_types                  false
% 6.84/1.48  --sat_finite_models                     false
% 6.84/1.48  --sat_fm_lemmas                         false
% 6.84/1.48  --sat_fm_prep                           false
% 6.84/1.48  --sat_fm_uc_incr                        true
% 6.84/1.48  --sat_out_model                         small
% 6.84/1.48  --sat_out_clauses                       false
% 6.84/1.48  
% 6.84/1.48  ------ QBF Options
% 6.84/1.48  
% 6.84/1.48  --qbf_mode                              false
% 6.84/1.48  --qbf_elim_univ                         false
% 6.84/1.48  --qbf_dom_inst                          none
% 6.84/1.48  --qbf_dom_pre_inst                      false
% 6.84/1.48  --qbf_sk_in                             false
% 6.84/1.48  --qbf_pred_elim                         true
% 6.84/1.48  --qbf_split                             512
% 6.84/1.48  
% 6.84/1.48  ------ BMC1 Options
% 6.84/1.48  
% 6.84/1.48  --bmc1_incremental                      false
% 6.84/1.48  --bmc1_axioms                           reachable_all
% 6.84/1.48  --bmc1_min_bound                        0
% 6.84/1.48  --bmc1_max_bound                        -1
% 6.84/1.48  --bmc1_max_bound_default                -1
% 6.84/1.48  --bmc1_symbol_reachability              true
% 6.84/1.48  --bmc1_property_lemmas                  false
% 6.84/1.48  --bmc1_k_induction                      false
% 6.84/1.48  --bmc1_non_equiv_states                 false
% 6.84/1.48  --bmc1_deadlock                         false
% 6.84/1.48  --bmc1_ucm                              false
% 6.84/1.48  --bmc1_add_unsat_core                   none
% 6.84/1.48  --bmc1_unsat_core_children              false
% 6.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.48  --bmc1_out_stat                         full
% 6.84/1.48  --bmc1_ground_init                      false
% 6.84/1.48  --bmc1_pre_inst_next_state              false
% 6.84/1.48  --bmc1_pre_inst_state                   false
% 6.84/1.48  --bmc1_pre_inst_reach_state             false
% 6.84/1.48  --bmc1_out_unsat_core                   false
% 6.84/1.48  --bmc1_aig_witness_out                  false
% 6.84/1.48  --bmc1_verbose                          false
% 6.84/1.48  --bmc1_dump_clauses_tptp                false
% 6.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.48  --bmc1_dump_file                        -
% 6.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.48  --bmc1_ucm_extend_mode                  1
% 6.84/1.48  --bmc1_ucm_init_mode                    2
% 6.84/1.48  --bmc1_ucm_cone_mode                    none
% 6.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.48  --bmc1_ucm_relax_model                  4
% 6.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.48  --bmc1_ucm_layered_model                none
% 6.84/1.48  --bmc1_ucm_max_lemma_size               10
% 6.84/1.48  
% 6.84/1.48  ------ AIG Options
% 6.84/1.48  
% 6.84/1.48  --aig_mode                              false
% 6.84/1.48  
% 6.84/1.48  ------ Instantiation Options
% 6.84/1.48  
% 6.84/1.48  --instantiation_flag                    true
% 6.84/1.48  --inst_sos_flag                         false
% 6.84/1.48  --inst_sos_phase                        true
% 6.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel_side                     num_symb
% 6.84/1.48  --inst_solver_per_active                1400
% 6.84/1.48  --inst_solver_calls_frac                1.
% 6.84/1.48  --inst_passive_queue_type               priority_queues
% 6.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.48  --inst_passive_queues_freq              [25;2]
% 6.84/1.48  --inst_dismatching                      true
% 6.84/1.48  --inst_eager_unprocessed_to_passive     true
% 6.84/1.48  --inst_prop_sim_given                   true
% 6.84/1.48  --inst_prop_sim_new                     false
% 6.84/1.48  --inst_subs_new                         false
% 6.84/1.48  --inst_eq_res_simp                      false
% 6.84/1.48  --inst_subs_given                       false
% 6.84/1.48  --inst_orphan_elimination               true
% 6.84/1.48  --inst_learning_loop_flag               true
% 6.84/1.48  --inst_learning_start                   3000
% 6.84/1.48  --inst_learning_factor                  2
% 6.84/1.48  --inst_start_prop_sim_after_learn       3
% 6.84/1.48  --inst_sel_renew                        solver
% 6.84/1.48  --inst_lit_activity_flag                true
% 6.84/1.48  --inst_restr_to_given                   false
% 6.84/1.48  --inst_activity_threshold               500
% 6.84/1.48  --inst_out_proof                        true
% 6.84/1.48  
% 6.84/1.48  ------ Resolution Options
% 6.84/1.48  
% 6.84/1.48  --resolution_flag                       true
% 6.84/1.48  --res_lit_sel                           adaptive
% 6.84/1.48  --res_lit_sel_side                      none
% 6.84/1.48  --res_ordering                          kbo
% 6.84/1.48  --res_to_prop_solver                    active
% 6.84/1.48  --res_prop_simpl_new                    false
% 6.84/1.48  --res_prop_simpl_given                  true
% 6.84/1.48  --res_passive_queue_type                priority_queues
% 6.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.48  --res_passive_queues_freq               [15;5]
% 6.84/1.48  --res_forward_subs                      full
% 6.84/1.48  --res_backward_subs                     full
% 6.84/1.48  --res_forward_subs_resolution           true
% 6.84/1.48  --res_backward_subs_resolution          true
% 6.84/1.48  --res_orphan_elimination                true
% 6.84/1.48  --res_time_limit                        2.
% 6.84/1.48  --res_out_proof                         true
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Options
% 6.84/1.48  
% 6.84/1.48  --superposition_flag                    true
% 6.84/1.48  --sup_passive_queue_type                priority_queues
% 6.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.48  --demod_completeness_check              fast
% 6.84/1.48  --demod_use_ground                      true
% 6.84/1.48  --sup_to_prop_solver                    passive
% 6.84/1.48  --sup_prop_simpl_new                    true
% 6.84/1.48  --sup_prop_simpl_given                  true
% 6.84/1.48  --sup_fun_splitting                     false
% 6.84/1.48  --sup_smt_interval                      50000
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Simplification Setup
% 6.84/1.48  
% 6.84/1.48  --sup_indices_passive                   []
% 6.84/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_full_bw                           [BwDemod]
% 6.84/1.48  --sup_immed_triv                        [TrivRules]
% 6.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_immed_bw_main                     []
% 6.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  
% 6.84/1.48  ------ Combination Options
% 6.84/1.48  
% 6.84/1.48  --comb_res_mult                         3
% 6.84/1.48  --comb_sup_mult                         2
% 6.84/1.48  --comb_inst_mult                        10
% 6.84/1.48  
% 6.84/1.48  ------ Debug Options
% 6.84/1.48  
% 6.84/1.48  --dbg_backtrace                         false
% 6.84/1.48  --dbg_dump_prop_clauses                 false
% 6.84/1.48  --dbg_dump_prop_clauses_file            -
% 6.84/1.48  --dbg_out_stat                          false
% 6.84/1.48  ------ Parsing...
% 6.84/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.84/1.48  ------ Proving...
% 6.84/1.48  ------ Problem Properties 
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  clauses                                 30
% 6.84/1.48  conjectures                             5
% 6.84/1.48  EPR                                     2
% 6.84/1.48  Horn                                    26
% 6.84/1.48  unary                                   7
% 6.84/1.48  binary                                  3
% 6.84/1.48  lits                                    96
% 6.84/1.48  lits eq                                 22
% 6.84/1.48  fd_pure                                 0
% 6.84/1.48  fd_pseudo                               0
% 6.84/1.48  fd_cond                                 3
% 6.84/1.48  fd_pseudo_cond                          0
% 6.84/1.48  AC symbols                              0
% 6.84/1.48  
% 6.84/1.48  ------ Schedule dynamic 5 is on 
% 6.84/1.48  
% 6.84/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  ------ 
% 6.84/1.48  Current options:
% 6.84/1.48  ------ 
% 6.84/1.48  
% 6.84/1.48  ------ Input Options
% 6.84/1.48  
% 6.84/1.48  --out_options                           all
% 6.84/1.48  --tptp_safe_out                         true
% 6.84/1.48  --problem_path                          ""
% 6.84/1.48  --include_path                          ""
% 6.84/1.48  --clausifier                            res/vclausify_rel
% 6.84/1.48  --clausifier_options                    --mode clausify
% 6.84/1.48  --stdin                                 false
% 6.84/1.48  --stats_out                             all
% 6.84/1.48  
% 6.84/1.48  ------ General Options
% 6.84/1.48  
% 6.84/1.48  --fof                                   false
% 6.84/1.48  --time_out_real                         305.
% 6.84/1.48  --time_out_virtual                      -1.
% 6.84/1.48  --symbol_type_check                     false
% 6.84/1.48  --clausify_out                          false
% 6.84/1.48  --sig_cnt_out                           false
% 6.84/1.48  --trig_cnt_out                          false
% 6.84/1.48  --trig_cnt_out_tolerance                1.
% 6.84/1.48  --trig_cnt_out_sk_spl                   false
% 6.84/1.48  --abstr_cl_out                          false
% 6.84/1.48  
% 6.84/1.48  ------ Global Options
% 6.84/1.48  
% 6.84/1.48  --schedule                              default
% 6.84/1.48  --add_important_lit                     false
% 6.84/1.48  --prop_solver_per_cl                    1000
% 6.84/1.48  --min_unsat_core                        false
% 6.84/1.48  --soft_assumptions                      false
% 6.84/1.48  --soft_lemma_size                       3
% 6.84/1.48  --prop_impl_unit_size                   0
% 6.84/1.48  --prop_impl_unit                        []
% 6.84/1.48  --share_sel_clauses                     true
% 6.84/1.48  --reset_solvers                         false
% 6.84/1.48  --bc_imp_inh                            [conj_cone]
% 6.84/1.48  --conj_cone_tolerance                   3.
% 6.84/1.48  --extra_neg_conj                        none
% 6.84/1.48  --large_theory_mode                     true
% 6.84/1.48  --prolific_symb_bound                   200
% 6.84/1.48  --lt_threshold                          2000
% 6.84/1.48  --clause_weak_htbl                      true
% 6.84/1.48  --gc_record_bc_elim                     false
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing Options
% 6.84/1.48  
% 6.84/1.48  --preprocessing_flag                    true
% 6.84/1.48  --time_out_prep_mult                    0.1
% 6.84/1.48  --splitting_mode                        input
% 6.84/1.48  --splitting_grd                         true
% 6.84/1.48  --splitting_cvd                         false
% 6.84/1.48  --splitting_cvd_svl                     false
% 6.84/1.48  --splitting_nvd                         32
% 6.84/1.48  --sub_typing                            true
% 6.84/1.48  --prep_gs_sim                           true
% 6.84/1.48  --prep_unflatten                        true
% 6.84/1.48  --prep_res_sim                          true
% 6.84/1.48  --prep_upred                            true
% 6.84/1.48  --prep_sem_filter                       exhaustive
% 6.84/1.48  --prep_sem_filter_out                   false
% 6.84/1.48  --pred_elim                             true
% 6.84/1.48  --res_sim_input                         true
% 6.84/1.48  --eq_ax_congr_red                       true
% 6.84/1.48  --pure_diseq_elim                       true
% 6.84/1.48  --brand_transform                       false
% 6.84/1.48  --non_eq_to_eq                          false
% 6.84/1.48  --prep_def_merge                        true
% 6.84/1.48  --prep_def_merge_prop_impl              false
% 6.84/1.48  --prep_def_merge_mbd                    true
% 6.84/1.48  --prep_def_merge_tr_red                 false
% 6.84/1.48  --prep_def_merge_tr_cl                  false
% 6.84/1.48  --smt_preprocessing                     true
% 6.84/1.48  --smt_ac_axioms                         fast
% 6.84/1.48  --preprocessed_out                      false
% 6.84/1.48  --preprocessed_stats                    false
% 6.84/1.48  
% 6.84/1.48  ------ Abstraction refinement Options
% 6.84/1.48  
% 6.84/1.48  --abstr_ref                             []
% 6.84/1.48  --abstr_ref_prep                        false
% 6.84/1.48  --abstr_ref_until_sat                   false
% 6.84/1.48  --abstr_ref_sig_restrict                funpre
% 6.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.48  --abstr_ref_under                       []
% 6.84/1.48  
% 6.84/1.48  ------ SAT Options
% 6.84/1.48  
% 6.84/1.48  --sat_mode                              false
% 6.84/1.48  --sat_fm_restart_options                ""
% 6.84/1.48  --sat_gr_def                            false
% 6.84/1.48  --sat_epr_types                         true
% 6.84/1.48  --sat_non_cyclic_types                  false
% 6.84/1.48  --sat_finite_models                     false
% 6.84/1.48  --sat_fm_lemmas                         false
% 6.84/1.48  --sat_fm_prep                           false
% 6.84/1.48  --sat_fm_uc_incr                        true
% 6.84/1.48  --sat_out_model                         small
% 6.84/1.48  --sat_out_clauses                       false
% 6.84/1.48  
% 6.84/1.48  ------ QBF Options
% 6.84/1.48  
% 6.84/1.48  --qbf_mode                              false
% 6.84/1.48  --qbf_elim_univ                         false
% 6.84/1.48  --qbf_dom_inst                          none
% 6.84/1.48  --qbf_dom_pre_inst                      false
% 6.84/1.48  --qbf_sk_in                             false
% 6.84/1.48  --qbf_pred_elim                         true
% 6.84/1.48  --qbf_split                             512
% 6.84/1.48  
% 6.84/1.48  ------ BMC1 Options
% 6.84/1.48  
% 6.84/1.48  --bmc1_incremental                      false
% 6.84/1.48  --bmc1_axioms                           reachable_all
% 6.84/1.48  --bmc1_min_bound                        0
% 6.84/1.48  --bmc1_max_bound                        -1
% 6.84/1.48  --bmc1_max_bound_default                -1
% 6.84/1.48  --bmc1_symbol_reachability              true
% 6.84/1.48  --bmc1_property_lemmas                  false
% 6.84/1.48  --bmc1_k_induction                      false
% 6.84/1.48  --bmc1_non_equiv_states                 false
% 6.84/1.48  --bmc1_deadlock                         false
% 6.84/1.48  --bmc1_ucm                              false
% 6.84/1.48  --bmc1_add_unsat_core                   none
% 6.84/1.48  --bmc1_unsat_core_children              false
% 6.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.48  --bmc1_out_stat                         full
% 6.84/1.48  --bmc1_ground_init                      false
% 6.84/1.48  --bmc1_pre_inst_next_state              false
% 6.84/1.48  --bmc1_pre_inst_state                   false
% 6.84/1.48  --bmc1_pre_inst_reach_state             false
% 6.84/1.48  --bmc1_out_unsat_core                   false
% 6.84/1.48  --bmc1_aig_witness_out                  false
% 6.84/1.48  --bmc1_verbose                          false
% 6.84/1.48  --bmc1_dump_clauses_tptp                false
% 6.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.48  --bmc1_dump_file                        -
% 6.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.48  --bmc1_ucm_extend_mode                  1
% 6.84/1.48  --bmc1_ucm_init_mode                    2
% 6.84/1.48  --bmc1_ucm_cone_mode                    none
% 6.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.48  --bmc1_ucm_relax_model                  4
% 6.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.48  --bmc1_ucm_layered_model                none
% 6.84/1.48  --bmc1_ucm_max_lemma_size               10
% 6.84/1.48  
% 6.84/1.48  ------ AIG Options
% 6.84/1.48  
% 6.84/1.48  --aig_mode                              false
% 6.84/1.48  
% 6.84/1.48  ------ Instantiation Options
% 6.84/1.48  
% 6.84/1.48  --instantiation_flag                    true
% 6.84/1.48  --inst_sos_flag                         false
% 6.84/1.48  --inst_sos_phase                        true
% 6.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel_side                     none
% 6.84/1.48  --inst_solver_per_active                1400
% 6.84/1.48  --inst_solver_calls_frac                1.
% 6.84/1.48  --inst_passive_queue_type               priority_queues
% 6.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.48  --inst_passive_queues_freq              [25;2]
% 6.84/1.48  --inst_dismatching                      true
% 6.84/1.48  --inst_eager_unprocessed_to_passive     true
% 6.84/1.48  --inst_prop_sim_given                   true
% 6.84/1.48  --inst_prop_sim_new                     false
% 6.84/1.48  --inst_subs_new                         false
% 6.84/1.48  --inst_eq_res_simp                      false
% 6.84/1.48  --inst_subs_given                       false
% 6.84/1.48  --inst_orphan_elimination               true
% 6.84/1.48  --inst_learning_loop_flag               true
% 6.84/1.48  --inst_learning_start                   3000
% 6.84/1.48  --inst_learning_factor                  2
% 6.84/1.48  --inst_start_prop_sim_after_learn       3
% 6.84/1.48  --inst_sel_renew                        solver
% 6.84/1.48  --inst_lit_activity_flag                true
% 6.84/1.48  --inst_restr_to_given                   false
% 6.84/1.48  --inst_activity_threshold               500
% 6.84/1.48  --inst_out_proof                        true
% 6.84/1.48  
% 6.84/1.48  ------ Resolution Options
% 6.84/1.48  
% 6.84/1.48  --resolution_flag                       false
% 6.84/1.48  --res_lit_sel                           adaptive
% 6.84/1.48  --res_lit_sel_side                      none
% 6.84/1.48  --res_ordering                          kbo
% 6.84/1.48  --res_to_prop_solver                    active
% 6.84/1.48  --res_prop_simpl_new                    false
% 6.84/1.48  --res_prop_simpl_given                  true
% 6.84/1.48  --res_passive_queue_type                priority_queues
% 6.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.48  --res_passive_queues_freq               [15;5]
% 6.84/1.48  --res_forward_subs                      full
% 6.84/1.48  --res_backward_subs                     full
% 6.84/1.48  --res_forward_subs_resolution           true
% 6.84/1.48  --res_backward_subs_resolution          true
% 6.84/1.48  --res_orphan_elimination                true
% 6.84/1.48  --res_time_limit                        2.
% 6.84/1.48  --res_out_proof                         true
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Options
% 6.84/1.48  
% 6.84/1.48  --superposition_flag                    true
% 6.84/1.48  --sup_passive_queue_type                priority_queues
% 6.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.48  --demod_completeness_check              fast
% 6.84/1.48  --demod_use_ground                      true
% 6.84/1.48  --sup_to_prop_solver                    passive
% 6.84/1.48  --sup_prop_simpl_new                    true
% 6.84/1.48  --sup_prop_simpl_given                  true
% 6.84/1.48  --sup_fun_splitting                     false
% 6.84/1.48  --sup_smt_interval                      50000
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Simplification Setup
% 6.84/1.48  
% 6.84/1.48  --sup_indices_passive                   []
% 6.84/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_full_bw                           [BwDemod]
% 6.84/1.48  --sup_immed_triv                        [TrivRules]
% 6.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_immed_bw_main                     []
% 6.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  
% 6.84/1.48  ------ Combination Options
% 6.84/1.48  
% 6.84/1.48  --comb_res_mult                         3
% 6.84/1.48  --comb_sup_mult                         2
% 6.84/1.48  --comb_inst_mult                        10
% 6.84/1.48  
% 6.84/1.48  ------ Debug Options
% 6.84/1.48  
% 6.84/1.48  --dbg_backtrace                         false
% 6.84/1.48  --dbg_dump_prop_clauses                 false
% 6.84/1.48  --dbg_dump_prop_clauses_file            -
% 6.84/1.48  --dbg_out_stat                          false
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  ------ Proving...
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  % SZS status Theorem for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48   Resolution empty clause
% 6.84/1.48  
% 6.84/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  fof(f12,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f34,plain,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.48    inference(ennf_transformation,[],[f12])).
% 6.84/1.48  
% 6.84/1.48  fof(f35,plain,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.48    inference(flattening,[],[f34])).
% 6.84/1.48  
% 6.84/1.48  fof(f67,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f35])).
% 6.84/1.48  
% 6.84/1.48  fof(f13,conjecture,(
% 6.84/1.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f14,negated_conjecture,(
% 6.84/1.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.48    inference(negated_conjecture,[],[f13])).
% 6.84/1.48  
% 6.84/1.48  fof(f15,plain,(
% 6.84/1.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.48    inference(pure_predicate_removal,[],[f14])).
% 6.84/1.48  
% 6.84/1.48  fof(f36,plain,(
% 6.84/1.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 6.84/1.48    inference(ennf_transformation,[],[f15])).
% 6.84/1.48  
% 6.84/1.48  fof(f37,plain,(
% 6.84/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 6.84/1.48    inference(flattening,[],[f36])).
% 6.84/1.48  
% 6.84/1.48  fof(f42,plain,(
% 6.84/1.48    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f41,plain,(
% 6.84/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f40,plain,(
% 6.84/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f43,plain,(
% 6.84/1.48    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 6.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f42,f41,f40])).
% 6.84/1.48  
% 6.84/1.48  fof(f73,plain,(
% 6.84/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f10,axiom,(
% 6.84/1.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f31,plain,(
% 6.84/1.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 6.84/1.48    inference(ennf_transformation,[],[f10])).
% 6.84/1.48  
% 6.84/1.48  fof(f64,plain,(
% 6.84/1.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f31])).
% 6.84/1.48  
% 6.84/1.48  fof(f70,plain,(
% 6.84/1.48    l1_struct_0(sK1)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f69,plain,(
% 6.84/1.48    l1_struct_0(sK0)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f6,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f24,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(ennf_transformation,[],[f6])).
% 6.84/1.48  
% 6.84/1.48  fof(f52,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f24])).
% 6.84/1.48  
% 6.84/1.48  fof(f74,plain,(
% 6.84/1.48    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f7,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f25,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(ennf_transformation,[],[f7])).
% 6.84/1.48  
% 6.84/1.48  fof(f26,plain,(
% 6.84/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(flattening,[],[f25])).
% 6.84/1.48  
% 6.84/1.48  fof(f38,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(nnf_transformation,[],[f26])).
% 6.84/1.48  
% 6.84/1.48  fof(f53,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f38])).
% 6.84/1.48  
% 6.84/1.48  fof(f5,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f23,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(ennf_transformation,[],[f5])).
% 6.84/1.48  
% 6.84/1.48  fof(f51,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f23])).
% 6.84/1.48  
% 6.84/1.48  fof(f72,plain,(
% 6.84/1.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f11,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f32,plain,(
% 6.84/1.48    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.48    inference(ennf_transformation,[],[f11])).
% 6.84/1.48  
% 6.84/1.48  fof(f33,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.48    inference(flattening,[],[f32])).
% 6.84/1.48  
% 6.84/1.48  fof(f65,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f33])).
% 6.84/1.48  
% 6.84/1.48  fof(f71,plain,(
% 6.84/1.48    v1_funct_1(sK2)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f75,plain,(
% 6.84/1.48    v2_funct_1(sK2)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f8,axiom,(
% 6.84/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f27,plain,(
% 6.84/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.48    inference(ennf_transformation,[],[f8])).
% 6.84/1.48  
% 6.84/1.48  fof(f28,plain,(
% 6.84/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.48    inference(flattening,[],[f27])).
% 6.84/1.48  
% 6.84/1.48  fof(f39,plain,(
% 6.84/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.48    inference(nnf_transformation,[],[f28])).
% 6.84/1.48  
% 6.84/1.48  fof(f60,plain,(
% 6.84/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f39])).
% 6.84/1.48  
% 6.84/1.48  fof(f82,plain,(
% 6.84/1.48    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.84/1.48    inference(equality_resolution,[],[f60])).
% 6.84/1.48  
% 6.84/1.48  fof(f76,plain,(
% 6.84/1.48    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 6.84/1.48    inference(cnf_transformation,[],[f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f4,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f22,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.48    inference(ennf_transformation,[],[f4])).
% 6.84/1.48  
% 6.84/1.48  fof(f50,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f22])).
% 6.84/1.48  
% 6.84/1.48  fof(f1,axiom,(
% 6.84/1.48    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f16,plain,(
% 6.84/1.48    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.48    inference(ennf_transformation,[],[f1])).
% 6.84/1.48  
% 6.84/1.48  fof(f17,plain,(
% 6.84/1.48    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.48    inference(flattening,[],[f16])).
% 6.84/1.48  
% 6.84/1.48  fof(f45,plain,(
% 6.84/1.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f17])).
% 6.84/1.48  
% 6.84/1.48  fof(f9,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f29,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.48    inference(ennf_transformation,[],[f9])).
% 6.84/1.48  
% 6.84/1.48  fof(f30,plain,(
% 6.84/1.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.48    inference(flattening,[],[f29])).
% 6.84/1.48  
% 6.84/1.48  fof(f62,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f30])).
% 6.84/1.48  
% 6.84/1.48  fof(f68,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f35])).
% 6.84/1.48  
% 6.84/1.48  fof(f63,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f30])).
% 6.84/1.48  
% 6.84/1.48  fof(f66,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f35])).
% 6.84/1.48  
% 6.84/1.48  fof(f2,axiom,(
% 6.84/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f18,plain,(
% 6.84/1.48    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.48    inference(ennf_transformation,[],[f2])).
% 6.84/1.48  
% 6.84/1.48  fof(f19,plain,(
% 6.84/1.48    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.48    inference(flattening,[],[f18])).
% 6.84/1.48  
% 6.84/1.48  fof(f48,plain,(
% 6.84/1.48    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f19])).
% 6.84/1.48  
% 6.84/1.48  fof(f3,axiom,(
% 6.84/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 6.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f20,plain,(
% 6.84/1.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.48    inference(ennf_transformation,[],[f3])).
% 6.84/1.48  
% 6.84/1.48  fof(f21,plain,(
% 6.84/1.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.48    inference(flattening,[],[f20])).
% 6.84/1.48  
% 6.84/1.48  fof(f49,plain,(
% 6.84/1.48    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f21])).
% 6.84/1.48  
% 6.84/1.48  fof(f46,plain,(
% 6.84/1.48    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f17])).
% 6.84/1.48  
% 6.84/1.48  fof(f57,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f38])).
% 6.84/1.48  
% 6.84/1.48  fof(f79,plain,(
% 6.84/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.84/1.48    inference(equality_resolution,[],[f57])).
% 6.84/1.48  
% 6.84/1.48  fof(f54,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f38])).
% 6.84/1.48  
% 6.84/1.48  fof(f81,plain,(
% 6.84/1.48    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.84/1.48    inference(equality_resolution,[],[f54])).
% 6.84/1.48  
% 6.84/1.48  fof(f56,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f38])).
% 6.84/1.48  
% 6.84/1.48  fof(f80,plain,(
% 6.84/1.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.84/1.48    inference(equality_resolution,[],[f56])).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | ~ v1_funct_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f67]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1078,plain,
% 6.84/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 6.84/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.48      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_28,negated_conjecture,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 6.84/1.48      inference(cnf_transformation,[],[f73]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1075,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20,plain,
% 6.84/1.48      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f64]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_31,negated_conjecture,
% 6.84/1.48      ( l1_struct_0(sK1) ),
% 6.84/1.48      inference(cnf_transformation,[],[f70]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_369,plain,
% 6.84/1.48      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 6.84/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_370,plain,
% 6.84/1.48      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 6.84/1.48      inference(unflattening,[status(thm)],[c_369]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_32,negated_conjecture,
% 6.84/1.48      ( l1_struct_0(sK0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f69]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_374,plain,
% 6.84/1.48      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 6.84/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_375,plain,
% 6.84/1.48      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 6.84/1.48      inference(unflattening,[status(thm)],[c_374]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1112,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_1075,c_370,c_375]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8,plain,
% 6.84/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f52]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1089,plain,
% 6.84/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1579,plain,
% 6.84/1.48      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1112,c_1089]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_27,negated_conjecture,
% 6.84/1.48      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 6.84/1.48      inference(cnf_transformation,[],[f74]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1109,plain,
% 6.84/1.48      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_27,c_370,c_375]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1751,plain,
% 6.84/1.48      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1579,c_1109]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1755,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1751,c_1112]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_14,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | k1_relset_1(X1,X2,X0) = X1
% 6.84/1.48      | k1_xboole_0 = X2 ),
% 6.84/1.48      inference(cnf_transformation,[],[f53]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1083,plain,
% 6.84/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 6.84/1.48      | k1_xboole_0 = X1
% 6.84/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3000,plain,
% 6.84/1.48      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1755,c_1083]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7,plain,
% 6.84/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f51]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1090,plain,
% 6.84/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1583,plain,
% 6.84/1.48      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1112,c_1090]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1874,plain,
% 6.84/1.48      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_1583,c_1751]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3001,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_3000,c_1874]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_29,negated_conjecture,
% 6.84/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f72]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1074,plain,
% 6.84/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1106,plain,
% 6.84/1.48      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_1074,c_370,c_375]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1756,plain,
% 6.84/1.48      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1751,c_1106]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3165,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0 | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(global_propositional_subsumption,[status(thm)],[c_3001,c_1756]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3166,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_3165]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1753,plain,
% 6.84/1.48      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1751,c_1579]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_21,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 6.84/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.48      inference(cnf_transformation,[],[f65]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1080,plain,
% 6.84/1.48      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 6.84/1.48      | k2_relset_1(X0,X1,X2) != X1
% 6.84/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.48      | v1_funct_1(X2) != iProver_top
% 6.84/1.48      | v2_funct_1(X2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3960,plain,
% 6.84/1.48      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1753,c_1080]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_30,negated_conjecture,
% 6.84/1.48      ( v1_funct_1(sK2) ),
% 6.84/1.48      inference(cnf_transformation,[],[f71]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_35,plain,
% 6.84/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_26,negated_conjecture,
% 6.84/1.48      ( v2_funct_1(sK2) ),
% 6.84/1.48      inference(cnf_transformation,[],[f75]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_38,plain,
% 6.84/1.48      ( v2_funct_1(sK2) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4171,plain,
% 6.84/1.48      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_3960,c_35,c_38,c_1755,c_1756]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_15,plain,
% 6.84/1.48      ( r2_funct_2(X0,X1,X2,X2)
% 6.84/1.48      | ~ v1_funct_2(X2,X0,X1)
% 6.84/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.84/1.48      | ~ v1_funct_1(X2) ),
% 6.84/1.48      inference(cnf_transformation,[],[f82]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_25,negated_conjecture,
% 6.84/1.48      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 6.84/1.48      inference(cnf_transformation,[],[f76]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_383,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 6.84/1.48      | u1_struct_0(sK1) != X2
% 6.84/1.48      | u1_struct_0(sK0) != X1
% 6.84/1.48      | sK2 != X0 ),
% 6.84/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_384,plain,
% 6.84/1.48      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 6.84/1.48      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.84/1.48      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 6.84/1.48      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 6.84/1.48      inference(unflattening,[status(thm)],[c_383]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1071,plain,
% 6.84/1.48      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 6.84/1.48      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1285,plain,
% 6.84/1.48      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_1071,c_370,c_375]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1754,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1751,c_1285]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4176,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_4171,c_1754]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4305,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3166,c_4176]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_37,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6,plain,
% 6.84/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f50]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1357,plain,
% 6.84/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.84/1.48      | v1_relat_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1358,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.84/1.48      | v1_relat_1(sK2) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1357]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1,plain,
% 6.84/1.48      ( ~ v1_relat_1(X0)
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | v1_funct_1(k2_funct_1(X0))
% 6.84/1.48      | ~ v2_funct_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f45]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1438,plain,
% 6.84/1.48      ( ~ v1_relat_1(sK2)
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | ~ v1_funct_1(sK2)
% 6.84/1.48      | ~ v2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1442,plain,
% 6.84/1.48      ( v1_relat_1(sK2) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1438]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.48      inference(cnf_transformation,[],[f62]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1081,plain,
% 6.84/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 6.84/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.48      | v1_funct_1(X2) != iProver_top
% 6.84/1.48      | v2_funct_1(X2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3993,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1753,c_1081]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_22,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.84/1.48      | ~ v1_funct_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f68]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1079,plain,
% 6.84/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 6.84/1.48      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4198,plain,
% 6.84/1.48      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4171,c_1079]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.48      inference(cnf_transformation,[],[f63]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1082,plain,
% 6.84/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 6.84/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 6.84/1.48      | v1_funct_1(X2) != iProver_top
% 6.84/1.48      | v2_funct_1(X2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4139,plain,
% 6.84/1.48      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1753,c_1082]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4441,plain,
% 6.84/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4198,c_35,c_38,c_1755,c_1756,c_4139]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_24,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f66]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1077,plain,
% 6.84/1.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.48      | v1_funct_1(X0) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4447,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4441,c_1077]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4452,plain,
% 6.84/1.48      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4441,c_1089]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1091,plain,
% 6.84/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.48      | v1_relat_1(X0) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1466,plain,
% 6.84/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1112,c_1091]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3,plain,
% 6.84/1.48      ( ~ v1_relat_1(X0)
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f48]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1094,plain,
% 6.84/1.48      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 6.84/1.48      | v1_relat_1(X0) != iProver_top
% 6.84/1.48      | v1_funct_1(X0) != iProver_top
% 6.84/1.48      | v2_funct_1(X0) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2781,plain,
% 6.84/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1466,c_1094]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1435,plain,
% 6.84/1.48      ( ~ v1_relat_1(sK2)
% 6.84/1.48      | ~ v1_funct_1(sK2)
% 6.84/1.48      | ~ v2_funct_1(sK2)
% 6.84/1.48      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3102,plain,
% 6.84/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_2781,c_30,c_28,c_26,c_1357,c_1435]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4454,plain,
% 6.84/1.48      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_4452,c_3102]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4482,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4454,c_1080]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5,plain,
% 6.84/1.48      ( ~ v1_relat_1(X0)
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f49]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1092,plain,
% 6.84/1.48      ( k2_funct_1(k2_funct_1(X0)) = X0
% 6.84/1.48      | v1_relat_1(X0) != iProver_top
% 6.84/1.48      | v1_funct_1(X0) != iProver_top
% 6.84/1.48      | v2_funct_1(X0) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2127,plain,
% 6.84/1.48      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1466,c_1092]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1433,plain,
% 6.84/1.48      ( ~ v1_relat_1(sK2)
% 6.84/1.48      | ~ v1_funct_1(sK2)
% 6.84/1.48      | ~ v2_funct_1(sK2)
% 6.84/1.48      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2406,plain,
% 6.84/1.48      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_2127,c_30,c_28,c_26,c_1357,c_1433]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4489,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 6.84/1.48      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_4482,c_2406]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_0,plain,
% 6.84/1.48      ( ~ v1_relat_1(X0)
% 6.84/1.48      | ~ v1_funct_1(X0)
% 6.84/1.48      | ~ v2_funct_1(X0)
% 6.84/1.48      | v2_funct_1(k2_funct_1(X0)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f46]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1439,plain,
% 6.84/1.48      ( ~ v1_relat_1(sK2)
% 6.84/1.48      | ~ v1_funct_1(sK2)
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | ~ v2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1440,plain,
% 6.84/1.48      ( v1_relat_1(sK2) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1439]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4945,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 6.84/1.48      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4489,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_1755,c_1756,
% 6.84/1.48                 c_3993,c_4139]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4949,plain,
% 6.84/1.48      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3166,c_4945]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4951,plain,
% 6.84/1.48      ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4305,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,
% 6.84/1.48                 c_4176,c_4447,c_4949]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4952,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_4951]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4959,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3166,c_4952]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4958,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_4952]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5150,plain,
% 6.84/1.48      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | k2_relat_1(sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4959,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,
% 6.84/1.48                 c_4139,c_4958]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5151,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_5150]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5157,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3166,c_5151]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5156,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1078,c_5151]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5174,plain,
% 6.84/1.48      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_5157,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993,
% 6.84/1.48                 c_4139,c_5156]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5188,plain,
% 6.84/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_1755]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_10,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.84/1.48      | k1_xboole_0 = X1
% 6.84/1.48      | k1_xboole_0 = X0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f79]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1087,plain,
% 6.84/1.48      ( k1_xboole_0 = X0
% 6.84/1.48      | k1_xboole_0 = X1
% 6.84/1.48      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5743,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5188,c_1087]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5191,plain,
% 6.84/1.48      ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_1756]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5970,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0 | k2_struct_0(sK0) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5743,c_5191]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5971,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_5970]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4708,plain,
% 6.84/1.48      ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4447,c_35,c_37,c_38,c_1358,c_1442,c_1755,c_1756,c_3993]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5178,plain,
% 6.84/1.48      ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4708]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5183,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4176]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5228,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(backward_subsumption_resolution,[status(thm)],[c_5178,c_5183]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8780,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != sK2
% 6.84/1.48      | sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_5228]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5189,plain,
% 6.84/1.48      ( k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_1753]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5979,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_5189]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6592,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5979,c_1082]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5976,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_5188]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5978,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_5191]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7083,plain,
% 6.84/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_6592,c_35,c_38,c_5976,c_5978]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7084,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_7083]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7097,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_7084,c_1089]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7125,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_relat_1(sK2)
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_7097,c_3102]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7268,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | k1_relat_1(sK2) != k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_7125,c_1080]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7276,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
% 6.84/1.48      | k1_relat_1(sK2) != k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_7268,c_2406]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.84/1.48      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f81]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1084,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6756,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5976,c_1084]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6893,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,[status(thm)],[c_6756,c_5978]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6894,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_6893]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5190,plain,
% 6.84/1.48      ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k1_relat_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_1874]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5977,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_5190]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6900,plain,
% 6.84/1.48      ( k1_relat_1(sK2) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_6894,c_5977]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6593,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top
% 6.84/1.48      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v2_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5979,c_1081]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7076,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_6593,c_35,c_38,c_5976,c_5978]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8013,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = sK2
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_7276,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_6900,c_7076,
% 6.84/1.48                 c_7084]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8792,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_8780,c_35,c_37,c_38,c_1358,c_1440,c_1442,c_6900,c_7076,
% 6.84/1.48                 c_7084,c_7276]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8802,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_8792]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5181,plain,
% 6.84/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4441]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4199,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 6.84/1.48      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 6.84/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4171,c_1078]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4308,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_4199,c_35,c_38,c_1755,c_1756,c_3993]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5182,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4308]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8799,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_8792]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8832,plain,
% 6.84/1.48      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_8802,c_35,c_37,c_38,c_1358,c_1442,c_5181,c_5182,c_8799]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8833,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_8832]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8841,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_5971,c_8833]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8838,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1078,c_8833]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8858,plain,
% 6.84/1.48      ( sK2 = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_8841,c_35,c_37,c_38,c_1358,c_1442,c_5181,c_5182,c_8838]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8877,plain,
% 6.84/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5188]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3770,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = X0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_1087]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7315,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = X0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_3770,c_1078]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7317,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = X0
% 6.84/1.48      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(X0,k1_xboole_0,X1)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_7315]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12213,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = X0
% 6.84/1.48      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(forward_subsumption_resolution,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_7317,c_1077,c_1078]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12216,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_8877,c_12213]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5184,plain,
% 6.84/1.48      ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4171]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8875,plain,
% 6.84/1.48      ( k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5184]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12221,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_12216,c_8875]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_588,plain,( X0 = X0 ),theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_621,plain,
% 6.84/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_588]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_589,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1477,plain,
% 6.84/1.48      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_589]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1478,plain,
% 6.84/1.48      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1477]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_592,plain,
% 6.84/1.48      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 6.84/1.48      theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1503,plain,
% 6.84/1.48      ( v1_funct_1(X0)
% 6.84/1.48      | ~ v1_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | X0 != k2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_592]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1807,plain,
% 6.84/1.48      ( v1_funct_1(k2_funct_1(X0))
% 6.84/1.48      | ~ v1_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | k2_funct_1(X0) != k2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1503]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1810,plain,
% 6.84/1.48      ( ~ v1_funct_1(k2_funct_1(sK2))
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0))
% 6.84/1.48      | k2_funct_1(k1_xboole_0) != k2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1807]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_590,plain,
% 6.84/1.48      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 6.84/1.48      theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1808,plain,
% 6.84/1.48      ( X0 != sK2 | k2_funct_1(X0) = k2_funct_1(sK2) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_590]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1813,plain,
% 6.84/1.48      ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2) | k1_xboole_0 != sK2 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1808]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8868,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5182]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8950,plain,
% 6.84/1.48      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) ),
% 6.84/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_8868]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8865,plain,
% 6.84/1.48      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5181]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13271,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_8865,c_7315]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13328,plain,
% 6.84/1.48      ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
% 6.84/1.48      | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
% 6.84/1.48      | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0 ),
% 6.84/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_13271]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17179,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_12221,c_30,c_35,c_28,c_37,c_26,c_38,c_621,c_1357,c_1358,
% 6.84/1.48                 c_1438,c_1442,c_1478,c_1810,c_1813,c_5181,c_5182,c_8838,
% 6.84/1.48                 c_8950,c_13328]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8861,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5228]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17201,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17179,c_8861]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18504,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17179,c_17201]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1809,plain,
% 6.84/1.48      ( k2_funct_1(X0) != k2_funct_1(sK2)
% 6.84/1.48      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1807]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1811,plain,
% 6.84/1.48      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
% 6.84/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1809]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18503,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_17201]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18611,plain,
% 6.84/1.48      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | k2_struct_0(sK0) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_18504,c_35,c_37,c_38,c_621,c_1358,c_1442,c_1478,c_1811,
% 6.84/1.48                 c_1813,c_5181,c_5182,c_8838,c_8865,c_8868,c_18503]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18612,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_18611]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18617,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1078,c_18612]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19128,plain,
% 6.84/1.48      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_18617,c_35,c_37,c_38,c_621,c_1358,c_1442,c_1478,c_1811,
% 6.84/1.48                 c_1813,c_5181,c_5182,c_8838,c_8865,c_8868]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19161,plain,
% 6.84/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19128,c_8877]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3774,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_1084]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7488,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_3774,c_1078]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7492,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,k2_tops_2(k1_xboole_0,X0,X1))) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_tops_2(k1_xboole_0,X0,X1)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_7488]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12042,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,k2_tops_2(k1_xboole_0,X0,X1))) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.48      inference(forward_subsumption_resolution,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_7492,c_1077,c_1078]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19634,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_19161,c_12042]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_36,plain,
% 6.84/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1365,plain,
% 6.84/1.48      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_592]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1366,plain,
% 6.84/1.48      ( X0 != sK2
% 6.84/1.48      | v1_funct_1(X0) = iProver_top
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1368,plain,
% 6.84/1.48      ( k1_xboole_0 != sK2
% 6.84/1.48      | v1_funct_1(sK2) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1366]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2098,plain,
% 6.84/1.48      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_589]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2099,plain,
% 6.84/1.48      ( u1_struct_0(sK1) != k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = u1_struct_0(sK1)
% 6.84/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_2098]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2686,plain,
% 6.84/1.48      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_588]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1757,plain,
% 6.84/1.48      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_1751,c_370]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5192,plain,
% 6.84/1.48      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_1757]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2689,plain,
% 6.84/1.48      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_589]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6581,plain,
% 6.84/1.48      ( X0 = u1_struct_0(sK0)
% 6.84/1.48      | X0 != k2_struct_0(sK0)
% 6.84/1.48      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_2689]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6582,plain,
% 6.84/1.48      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 = u1_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 != k2_struct_0(sK0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_6581]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_601,plain,
% 6.84/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.48      | v1_funct_2(X3,X4,X5)
% 6.84/1.48      | X3 != X0
% 6.84/1.48      | X4 != X1
% 6.84/1.48      | X5 != X2 ),
% 6.84/1.48      theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1413,plain,
% 6.84/1.48      ( v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.84/1.48      | X2 != u1_struct_0(sK1)
% 6.84/1.48      | X1 != u1_struct_0(sK0)
% 6.84/1.48      | X0 != sK2 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_601]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7234,plain,
% 6.84/1.48      ( v1_funct_2(X0,u1_struct_0(sK0),X1)
% 6.84/1.48      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.84/1.48      | X1 != u1_struct_0(sK1)
% 6.84/1.48      | X0 != sK2
% 6.84/1.48      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1413]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7235,plain,
% 6.84/1.48      ( X0 != u1_struct_0(sK1)
% 6.84/1.48      | X1 != sK2
% 6.84/1.48      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 6.84/1.48      | v1_funct_2(X1,u1_struct_0(sK0),X0) = iProver_top
% 6.84/1.48      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_7234]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7237,plain,
% 6.84/1.48      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 != u1_struct_0(sK1)
% 6.84/1.48      | k1_xboole_0 != sK2
% 6.84/1.48      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.84/1.48      | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_7235]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7386,plain,
% 6.84/1.48      ( X0 != X1 | X0 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_589]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7387,plain,
% 6.84/1.48      ( k2_struct_0(sK0) != k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = k2_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_7386]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7651,plain,
% 6.84/1.48      ( v1_funct_2(X0,X1,X2)
% 6.84/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK0),X4)
% 6.84/1.48      | X0 != X3
% 6.84/1.48      | X2 != X4
% 6.84/1.48      | X1 != u1_struct_0(sK0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_601]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7652,plain,
% 6.84/1.48      ( X0 != X1
% 6.84/1.48      | X2 != X3
% 6.84/1.48      | X4 != u1_struct_0(sK0)
% 6.84/1.48      | v1_funct_2(X0,X4,X2) = iProver_top
% 6.84/1.48      | v1_funct_2(X1,u1_struct_0(sK0),X3) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_7651]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_7654,plain,
% 6.84/1.48      ( k1_xboole_0 != u1_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 != k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_7652]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12044,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_12042]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20333,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_19634,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1368,
% 6.84/1.48                 c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,
% 6.84/1.48                 c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_12044,c_18617,
% 6.84/1.48                 c_19161]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19159,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19128,c_8875]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20335,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))) = k1_xboole_0 ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_20333,c_19159]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_11,plain,
% 6.84/1.48      ( v1_funct_2(X0,k1_xboole_0,X1)
% 6.84/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.84/1.48      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f80]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1086,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 6.84/1.48      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 6.84/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20338,plain,
% 6.84/1.48      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) = iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_20335,c_1086]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19145,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19128,c_8861]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5177,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 6.84/1.48      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_5174,c_4945]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8864,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5177]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19152,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19128,c_8864]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19636,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_19161,c_1084]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8878,plain,
% 6.84/1.48      ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_5190]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19162,plain,
% 6.84/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19128,c_8878]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19655,plain,
% 6.84/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19636,c_19162]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20719,plain,
% 6.84/1.48      ( m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_20338,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,
% 6.84/1.48                 c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,
% 6.84/1.48                 c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,c_19145,c_19152,
% 6.84/1.48                 c_19655]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3773,plain,
% 6.84/1.48      ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
% 6.84/1.48      | v1_funct_2(X2,X1,X0) != iProver_top
% 6.84/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 6.84/1.48      | v1_funct_1(X2) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1079,c_1089]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19639,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_19161,c_3773]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1414,plain,
% 6.84/1.48      ( X0 != u1_struct_0(sK1)
% 6.84/1.48      | X1 != u1_struct_0(sK0)
% 6.84/1.48      | X2 != sK2
% 6.84/1.48      | v1_funct_2(X2,X1,X0) = iProver_top
% 6.84/1.48      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1413]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1416,plain,
% 6.84/1.48      ( k1_xboole_0 != u1_struct_0(sK1)
% 6.84/1.48      | k1_xboole_0 != u1_struct_0(sK0)
% 6.84/1.48      | k1_xboole_0 != sK2
% 6.84/1.48      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1414]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3872,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 6.84/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_3773]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20345,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_19639,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1368,
% 6.84/1.48                 c_1416,c_1442,c_1478,c_1811,c_1813,c_2099,c_3872,c_5181,
% 6.84/1.48                 c_5182,c_5192,c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,
% 6.84/1.48                 c_19161]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19773,plain,
% 6.84/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_19655,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,
% 6.84/1.48                 c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,
% 6.84/1.48                 c_6582,c_7387,c_8838,c_8865,c_8868,c_18617]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8884,plain,
% 6.84/1.48      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_3102]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19777,plain,
% 6.84/1.48      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_19773,c_8884]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20347,plain,
% 6.84/1.48      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_20345,c_19159,c_19777]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20351,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k2_funct_1(k2_funct_1(k1_xboole_0))
% 6.84/1.48      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_20347,c_1080]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8885,plain,
% 6.84/1.48      ( k2_funct_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_8858,c_2406]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20357,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.48      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.48      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 6.84/1.48      | v2_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_20351,c_8885]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20536,plain,
% 6.84/1.48      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_20357,c_35,c_36,c_37,c_38,c_375,c_621,c_1358,c_1416,
% 6.84/1.48                 c_1442,c_1478,c_1811,c_1813,c_2099,c_5181,c_5182,c_5192,
% 6.84/1.48                 c_6582,c_7387,c_8838,c_8865,c_8868,c_18617,c_19152,c_19655]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20723,plain,
% 6.84/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_20719,c_20536]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20725,plain,
% 6.84/1.48      ( $false ),
% 6.84/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_20723,c_19161]) ).
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  ------                               Statistics
% 6.84/1.48  
% 6.84/1.48  ------ General
% 6.84/1.48  
% 6.84/1.48  abstr_ref_over_cycles:                  0
% 6.84/1.48  abstr_ref_under_cycles:                 0
% 6.84/1.48  gc_basic_clause_elim:                   0
% 6.84/1.48  forced_gc_time:                         0
% 6.84/1.48  parsing_time:                           0.012
% 6.84/1.48  unif_index_cands_time:                  0.
% 6.84/1.48  unif_index_add_time:                    0.
% 6.84/1.48  orderings_time:                         0.
% 6.84/1.48  out_proof_time:                         0.021
% 6.84/1.48  total_time:                             0.613
% 6.84/1.48  num_of_symbols:                         52
% 6.84/1.48  num_of_terms:                           12645
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing
% 6.84/1.48  
% 6.84/1.48  num_of_splits:                          0
% 6.84/1.48  num_of_split_atoms:                     0
% 6.84/1.48  num_of_reused_defs:                     0
% 6.84/1.48  num_eq_ax_congr_red:                    6
% 6.84/1.48  num_of_sem_filtered_clauses:            1
% 6.84/1.48  num_of_subtypes:                        0
% 6.84/1.48  monotx_restored_types:                  0
% 6.84/1.48  sat_num_of_epr_types:                   0
% 6.84/1.48  sat_num_of_non_cyclic_types:            0
% 6.84/1.48  sat_guarded_non_collapsed_types:        0
% 6.84/1.48  num_pure_diseq_elim:                    0
% 6.84/1.48  simp_replaced_by:                       0
% 6.84/1.48  res_preprocessed:                       158
% 6.84/1.48  prep_upred:                             0
% 6.84/1.48  prep_unflattend:                        9
% 6.84/1.48  smt_new_axioms:                         0
% 6.84/1.48  pred_elim_cands:                        5
% 6.84/1.48  pred_elim:                              2
% 6.84/1.48  pred_elim_cl:                           3
% 6.84/1.48  pred_elim_cycles:                       4
% 6.84/1.48  merged_defs:                            0
% 6.84/1.48  merged_defs_ncl:                        0
% 6.84/1.48  bin_hyper_res:                          0
% 6.84/1.48  prep_cycles:                            4
% 6.84/1.48  pred_elim_time:                         0.004
% 6.84/1.48  splitting_time:                         0.
% 6.84/1.48  sem_filter_time:                        0.
% 6.84/1.48  monotx_time:                            0.001
% 6.84/1.48  subtype_inf_time:                       0.
% 6.84/1.48  
% 6.84/1.48  ------ Problem properties
% 6.84/1.48  
% 6.84/1.48  clauses:                                30
% 6.84/1.48  conjectures:                            5
% 6.84/1.48  epr:                                    2
% 6.84/1.48  horn:                                   26
% 6.84/1.48  ground:                                 8
% 6.84/1.48  unary:                                  7
% 6.84/1.48  binary:                                 3
% 6.84/1.48  lits:                                   96
% 6.84/1.48  lits_eq:                                22
% 6.84/1.48  fd_pure:                                0
% 6.84/1.48  fd_pseudo:                              0
% 6.84/1.48  fd_cond:                                3
% 6.84/1.48  fd_pseudo_cond:                         0
% 6.84/1.48  ac_symbols:                             0
% 6.84/1.48  
% 6.84/1.48  ------ Propositional Solver
% 6.84/1.48  
% 6.84/1.48  prop_solver_calls:                      32
% 6.84/1.48  prop_fast_solver_calls:                 2370
% 6.84/1.48  smt_solver_calls:                       0
% 6.84/1.48  smt_fast_solver_calls:                  0
% 6.84/1.48  prop_num_of_clauses:                    6598
% 6.84/1.48  prop_preprocess_simplified:             11301
% 6.84/1.48  prop_fo_subsumed:                       291
% 6.84/1.48  prop_solver_time:                       0.
% 6.84/1.48  smt_solver_time:                        0.
% 6.84/1.48  smt_fast_solver_time:                   0.
% 6.84/1.48  prop_fast_solver_time:                  0.
% 6.84/1.48  prop_unsat_core_time:                   0.
% 6.84/1.48  
% 6.84/1.48  ------ QBF
% 6.84/1.48  
% 6.84/1.48  qbf_q_res:                              0
% 6.84/1.48  qbf_num_tautologies:                    0
% 6.84/1.48  qbf_prep_cycles:                        0
% 6.84/1.48  
% 6.84/1.48  ------ BMC1
% 6.84/1.48  
% 6.84/1.48  bmc1_current_bound:                     -1
% 6.84/1.48  bmc1_last_solved_bound:                 -1
% 6.84/1.48  bmc1_unsat_core_size:                   -1
% 6.84/1.48  bmc1_unsat_core_parents_size:           -1
% 6.84/1.48  bmc1_merge_next_fun:                    0
% 6.84/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.84/1.48  
% 6.84/1.48  ------ Instantiation
% 6.84/1.48  
% 6.84/1.48  inst_num_of_clauses:                    2158
% 6.84/1.48  inst_num_in_passive:                    693
% 6.84/1.48  inst_num_in_active:                     1006
% 6.84/1.48  inst_num_in_unprocessed:                459
% 6.84/1.48  inst_num_of_loops:                      1130
% 6.84/1.48  inst_num_of_learning_restarts:          0
% 6.84/1.48  inst_num_moves_active_passive:          118
% 6.84/1.48  inst_lit_activity:                      0
% 6.84/1.48  inst_lit_activity_moves:                0
% 6.84/1.48  inst_num_tautologies:                   0
% 6.84/1.48  inst_num_prop_implied:                  0
% 6.84/1.48  inst_num_existing_simplified:           0
% 6.84/1.48  inst_num_eq_res_simplified:             0
% 6.84/1.48  inst_num_child_elim:                    0
% 6.84/1.48  inst_num_of_dismatching_blockings:      644
% 6.84/1.48  inst_num_of_non_proper_insts:           1595
% 6.84/1.48  inst_num_of_duplicates:                 0
% 6.84/1.48  inst_inst_num_from_inst_to_res:         0
% 6.84/1.48  inst_dismatching_checking_time:         0.
% 6.84/1.48  
% 6.84/1.48  ------ Resolution
% 6.84/1.48  
% 6.84/1.48  res_num_of_clauses:                     0
% 6.84/1.48  res_num_in_passive:                     0
% 6.84/1.48  res_num_in_active:                      0
% 6.84/1.48  res_num_of_loops:                       162
% 6.84/1.48  res_forward_subset_subsumed:            84
% 6.84/1.48  res_backward_subset_subsumed:           4
% 6.84/1.48  res_forward_subsumed:                   0
% 6.84/1.48  res_backward_subsumed:                  0
% 6.84/1.48  res_forward_subsumption_resolution:     0
% 6.84/1.48  res_backward_subsumption_resolution:    0
% 6.84/1.48  res_clause_to_clause_subsumption:       2186
% 6.84/1.48  res_orphan_elimination:                 0
% 6.84/1.48  res_tautology_del:                      155
% 6.84/1.48  res_num_eq_res_simplified:              0
% 6.84/1.48  res_num_sel_changes:                    0
% 6.84/1.48  res_moves_from_active_to_pass:          0
% 6.84/1.48  
% 6.84/1.48  ------ Superposition
% 6.84/1.48  
% 6.84/1.48  sup_time_total:                         0.
% 6.84/1.48  sup_time_generating:                    0.
% 6.84/1.48  sup_time_sim_full:                      0.
% 6.84/1.48  sup_time_sim_immed:                     0.
% 6.84/1.48  
% 6.84/1.48  sup_num_of_clauses:                     234
% 6.84/1.48  sup_num_in_active:                      108
% 6.84/1.48  sup_num_in_passive:                     126
% 6.84/1.48  sup_num_of_loops:                       224
% 6.84/1.48  sup_fw_superposition:                   325
% 6.84/1.48  sup_bw_superposition:                   373
% 6.84/1.48  sup_immediate_simplified:               317
% 6.84/1.48  sup_given_eliminated:                   0
% 6.84/1.48  comparisons_done:                       0
% 6.84/1.48  comparisons_avoided:                    18
% 6.84/1.48  
% 6.84/1.48  ------ Simplifications
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  sim_fw_subset_subsumed:                 137
% 6.84/1.48  sim_bw_subset_subsumed:                 64
% 6.84/1.48  sim_fw_subsumed:                        32
% 6.84/1.48  sim_bw_subsumed:                        2
% 6.84/1.48  sim_fw_subsumption_res:                 30
% 6.84/1.48  sim_bw_subsumption_res:                 1
% 6.84/1.48  sim_tautology_del:                      3
% 6.84/1.48  sim_eq_tautology_del:                   167
% 6.84/1.48  sim_eq_res_simp:                        0
% 6.84/1.48  sim_fw_demodulated:                     1
% 6.84/1.48  sim_bw_demodulated:                     97
% 6.84/1.48  sim_light_normalised:                   224
% 6.84/1.48  sim_joinable_taut:                      0
% 6.84/1.48  sim_joinable_simp:                      0
% 6.84/1.48  sim_ac_normalised:                      0
% 6.84/1.48  sim_smt_subsumption:                    0
% 6.84/1.48  
%------------------------------------------------------------------------------
