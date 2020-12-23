%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:28 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  171 (9246 expanded)
%              Number of clauses        :  105 (2524 expanded)
%              Number of leaves         :   17 (2806 expanded)
%              Depth                    :   22
%              Number of atoms          :  612 (60830 expanded)
%              Number of equality atoms :  259 (10699 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
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
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40,f39])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f10])).

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
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1060,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_383,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_384,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_388,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_389,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_1096,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1060,c_384,c_389])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1071,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1519,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1096,c_1071])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1093,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_25,c_384,c_389])).

cnf(c_1685,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1519,c_1093])).

cnf(c_1802,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1685,c_1096])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1065,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3770,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1065])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1072,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1523,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1096,c_1072])).

cnf(c_1922,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1523,c_1685])).

cnf(c_3771,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3770,c_1922])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1059,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1090,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1059,c_384,c_389])).

cnf(c_1803,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1685,c_1090])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_356,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_374,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_356,c_30])).

cnf(c_375,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_29])).

cnf(c_1805,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1685,c_377])).

cnf(c_3951,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3771,c_1803,c_1805])).

cnf(c_1800,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1685,c_1519])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1062,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2212,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1062])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2612,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_35,c_38,c_1802,c_1803])).

cnf(c_16,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_396,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_596,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_396])).

cnf(c_1055,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1254,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1055,c_384,c_389])).

cnf(c_595,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_396])).

cnf(c_1056,plain,
    ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1209,plain,
    ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1056,c_384,c_389])).

cnf(c_1260,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1254,c_1209])).

cnf(c_2489,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1260,c_1685])).

cnf(c_2615,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2612,c_2489])).

cnf(c_3955,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3951,c_2615])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1327,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1390,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1391,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1389,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1393,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1064,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3743,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1064])).

cnf(c_3880,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3743,c_35,c_38,c_1802,c_1803])).

cnf(c_3954,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3951,c_3880])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1063,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2624,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1063])).

cnf(c_3173,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2624,c_35,c_38,c_1802,c_1803])).

cnf(c_3956,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3951,c_3173])).

cnf(c_3889,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3880,c_1071])).

cnf(c_1073,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1417,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1073])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1076,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2781,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1076])).

cnf(c_1385,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3034,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2781,c_28,c_26,c_24,c_1326,c_1385])).

cnf(c_3891,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3889,c_3034])).

cnf(c_4883,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3891,c_3951])).

cnf(c_4887,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_1062])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1074,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2018,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1074])).

cnf(c_1386,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2496,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2018,c_28,c_26,c_24,c_1326,c_1386])).

cnf(c_4893,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4887,c_2496])).

cnf(c_5145,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3955,c_35,c_37,c_38,c_1327,c_1391,c_1393,c_3954,c_3956,c_4893])).

cnf(c_4927,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_35,c_37,c_38,c_1327,c_1391,c_1393,c_3954,c_3956])).

cnf(c_5149,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5145,c_4927])).

cnf(c_1058,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3958,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3951,c_1802])).

cnf(c_3961,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3951,c_1803])).

cnf(c_5153,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5149,c_1058,c_3958,c_3961])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.10/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.95  
% 3.10/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.95  
% 3.10/0.95  ------  iProver source info
% 3.10/0.95  
% 3.10/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.95  git: non_committed_changes: false
% 3.10/0.95  git: last_make_outside_of_git: false
% 3.10/0.95  
% 3.10/0.95  ------ 
% 3.10/0.95  
% 3.10/0.95  ------ Input Options
% 3.10/0.95  
% 3.10/0.95  --out_options                           all
% 3.10/0.95  --tptp_safe_out                         true
% 3.10/0.95  --problem_path                          ""
% 3.10/0.95  --include_path                          ""
% 3.10/0.95  --clausifier                            res/vclausify_rel
% 3.10/0.95  --clausifier_options                    --mode clausify
% 3.10/0.95  --stdin                                 false
% 3.10/0.95  --stats_out                             all
% 3.10/0.95  
% 3.10/0.95  ------ General Options
% 3.10/0.95  
% 3.10/0.95  --fof                                   false
% 3.10/0.95  --time_out_real                         305.
% 3.10/0.95  --time_out_virtual                      -1.
% 3.10/0.95  --symbol_type_check                     false
% 3.10/0.95  --clausify_out                          false
% 3.10/0.95  --sig_cnt_out                           false
% 3.10/0.95  --trig_cnt_out                          false
% 3.10/0.95  --trig_cnt_out_tolerance                1.
% 3.10/0.95  --trig_cnt_out_sk_spl                   false
% 3.10/0.95  --abstr_cl_out                          false
% 3.10/0.95  
% 3.10/0.95  ------ Global Options
% 3.10/0.95  
% 3.10/0.95  --schedule                              default
% 3.10/0.95  --add_important_lit                     false
% 3.10/0.95  --prop_solver_per_cl                    1000
% 3.10/0.95  --min_unsat_core                        false
% 3.10/0.95  --soft_assumptions                      false
% 3.10/0.95  --soft_lemma_size                       3
% 3.10/0.95  --prop_impl_unit_size                   0
% 3.10/0.95  --prop_impl_unit                        []
% 3.10/0.95  --share_sel_clauses                     true
% 3.10/0.95  --reset_solvers                         false
% 3.10/0.95  --bc_imp_inh                            [conj_cone]
% 3.10/0.95  --conj_cone_tolerance                   3.
% 3.10/0.95  --extra_neg_conj                        none
% 3.10/0.95  --large_theory_mode                     true
% 3.10/0.95  --prolific_symb_bound                   200
% 3.10/0.95  --lt_threshold                          2000
% 3.10/0.95  --clause_weak_htbl                      true
% 3.10/0.95  --gc_record_bc_elim                     false
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing Options
% 3.10/0.95  
% 3.10/0.95  --preprocessing_flag                    true
% 3.10/0.95  --time_out_prep_mult                    0.1
% 3.10/0.95  --splitting_mode                        input
% 3.10/0.95  --splitting_grd                         true
% 3.10/0.95  --splitting_cvd                         false
% 3.10/0.95  --splitting_cvd_svl                     false
% 3.10/0.95  --splitting_nvd                         32
% 3.10/0.95  --sub_typing                            true
% 3.10/0.95  --prep_gs_sim                           true
% 3.10/0.95  --prep_unflatten                        true
% 3.10/0.95  --prep_res_sim                          true
% 3.10/0.95  --prep_upred                            true
% 3.10/0.95  --prep_sem_filter                       exhaustive
% 3.10/0.95  --prep_sem_filter_out                   false
% 3.10/0.95  --pred_elim                             true
% 3.10/0.95  --res_sim_input                         true
% 3.10/0.95  --eq_ax_congr_red                       true
% 3.10/0.95  --pure_diseq_elim                       true
% 3.10/0.95  --brand_transform                       false
% 3.10/0.95  --non_eq_to_eq                          false
% 3.10/0.95  --prep_def_merge                        true
% 3.10/0.95  --prep_def_merge_prop_impl              false
% 3.10/0.95  --prep_def_merge_mbd                    true
% 3.10/0.95  --prep_def_merge_tr_red                 false
% 3.10/0.95  --prep_def_merge_tr_cl                  false
% 3.10/0.95  --smt_preprocessing                     true
% 3.10/0.95  --smt_ac_axioms                         fast
% 3.10/0.95  --preprocessed_out                      false
% 3.10/0.95  --preprocessed_stats                    false
% 3.10/0.95  
% 3.10/0.95  ------ Abstraction refinement Options
% 3.10/0.95  
% 3.10/0.95  --abstr_ref                             []
% 3.10/0.95  --abstr_ref_prep                        false
% 3.10/0.95  --abstr_ref_until_sat                   false
% 3.10/0.95  --abstr_ref_sig_restrict                funpre
% 3.10/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.95  --abstr_ref_under                       []
% 3.10/0.95  
% 3.10/0.95  ------ SAT Options
% 3.10/0.95  
% 3.10/0.95  --sat_mode                              false
% 3.10/0.95  --sat_fm_restart_options                ""
% 3.10/0.95  --sat_gr_def                            false
% 3.10/0.95  --sat_epr_types                         true
% 3.10/0.95  --sat_non_cyclic_types                  false
% 3.10/0.95  --sat_finite_models                     false
% 3.10/0.95  --sat_fm_lemmas                         false
% 3.10/0.95  --sat_fm_prep                           false
% 3.10/0.95  --sat_fm_uc_incr                        true
% 3.10/0.95  --sat_out_model                         small
% 3.10/0.95  --sat_out_clauses                       false
% 3.10/0.95  
% 3.10/0.95  ------ QBF Options
% 3.10/0.95  
% 3.10/0.95  --qbf_mode                              false
% 3.10/0.95  --qbf_elim_univ                         false
% 3.10/0.95  --qbf_dom_inst                          none
% 3.10/0.95  --qbf_dom_pre_inst                      false
% 3.10/0.95  --qbf_sk_in                             false
% 3.10/0.95  --qbf_pred_elim                         true
% 3.10/0.95  --qbf_split                             512
% 3.10/0.95  
% 3.10/0.95  ------ BMC1 Options
% 3.10/0.95  
% 3.10/0.95  --bmc1_incremental                      false
% 3.10/0.95  --bmc1_axioms                           reachable_all
% 3.10/0.95  --bmc1_min_bound                        0
% 3.10/0.95  --bmc1_max_bound                        -1
% 3.10/0.95  --bmc1_max_bound_default                -1
% 3.10/0.95  --bmc1_symbol_reachability              true
% 3.10/0.95  --bmc1_property_lemmas                  false
% 3.10/0.95  --bmc1_k_induction                      false
% 3.10/0.95  --bmc1_non_equiv_states                 false
% 3.10/0.95  --bmc1_deadlock                         false
% 3.10/0.95  --bmc1_ucm                              false
% 3.10/0.95  --bmc1_add_unsat_core                   none
% 3.10/0.95  --bmc1_unsat_core_children              false
% 3.10/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.95  --bmc1_out_stat                         full
% 3.10/0.95  --bmc1_ground_init                      false
% 3.10/0.95  --bmc1_pre_inst_next_state              false
% 3.10/0.95  --bmc1_pre_inst_state                   false
% 3.10/0.95  --bmc1_pre_inst_reach_state             false
% 3.10/0.95  --bmc1_out_unsat_core                   false
% 3.10/0.95  --bmc1_aig_witness_out                  false
% 3.10/0.95  --bmc1_verbose                          false
% 3.10/0.95  --bmc1_dump_clauses_tptp                false
% 3.10/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.95  --bmc1_dump_file                        -
% 3.10/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.95  --bmc1_ucm_extend_mode                  1
% 3.10/0.95  --bmc1_ucm_init_mode                    2
% 3.10/0.95  --bmc1_ucm_cone_mode                    none
% 3.10/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.95  --bmc1_ucm_relax_model                  4
% 3.10/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.95  --bmc1_ucm_layered_model                none
% 3.10/0.95  --bmc1_ucm_max_lemma_size               10
% 3.10/0.95  
% 3.10/0.95  ------ AIG Options
% 3.10/0.95  
% 3.10/0.95  --aig_mode                              false
% 3.10/0.95  
% 3.10/0.95  ------ Instantiation Options
% 3.10/0.95  
% 3.10/0.95  --instantiation_flag                    true
% 3.10/0.95  --inst_sos_flag                         false
% 3.10/0.95  --inst_sos_phase                        true
% 3.10/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.95  --inst_lit_sel_side                     num_symb
% 3.10/0.95  --inst_solver_per_active                1400
% 3.10/0.95  --inst_solver_calls_frac                1.
% 3.10/0.95  --inst_passive_queue_type               priority_queues
% 3.10/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.95  --inst_passive_queues_freq              [25;2]
% 3.10/0.95  --inst_dismatching                      true
% 3.10/0.95  --inst_eager_unprocessed_to_passive     true
% 3.10/0.95  --inst_prop_sim_given                   true
% 3.10/0.95  --inst_prop_sim_new                     false
% 3.10/0.95  --inst_subs_new                         false
% 3.10/0.95  --inst_eq_res_simp                      false
% 3.10/0.95  --inst_subs_given                       false
% 3.10/0.95  --inst_orphan_elimination               true
% 3.10/0.95  --inst_learning_loop_flag               true
% 3.10/0.95  --inst_learning_start                   3000
% 3.10/0.95  --inst_learning_factor                  2
% 3.10/0.95  --inst_start_prop_sim_after_learn       3
% 3.10/0.95  --inst_sel_renew                        solver
% 3.10/0.95  --inst_lit_activity_flag                true
% 3.10/0.95  --inst_restr_to_given                   false
% 3.10/0.95  --inst_activity_threshold               500
% 3.10/0.95  --inst_out_proof                        true
% 3.10/0.95  
% 3.10/0.95  ------ Resolution Options
% 3.10/0.95  
% 3.10/0.95  --resolution_flag                       true
% 3.10/0.95  --res_lit_sel                           adaptive
% 3.10/0.95  --res_lit_sel_side                      none
% 3.10/0.95  --res_ordering                          kbo
% 3.10/0.95  --res_to_prop_solver                    active
% 3.10/0.95  --res_prop_simpl_new                    false
% 3.10/0.95  --res_prop_simpl_given                  true
% 3.10/0.95  --res_passive_queue_type                priority_queues
% 3.10/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.95  --res_passive_queues_freq               [15;5]
% 3.10/0.95  --res_forward_subs                      full
% 3.10/0.95  --res_backward_subs                     full
% 3.10/0.95  --res_forward_subs_resolution           true
% 3.10/0.95  --res_backward_subs_resolution          true
% 3.10/0.95  --res_orphan_elimination                true
% 3.10/0.95  --res_time_limit                        2.
% 3.10/0.95  --res_out_proof                         true
% 3.10/0.95  
% 3.10/0.95  ------ Superposition Options
% 3.10/0.95  
% 3.10/0.95  --superposition_flag                    true
% 3.10/0.95  --sup_passive_queue_type                priority_queues
% 3.10/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.95  --demod_completeness_check              fast
% 3.10/0.95  --demod_use_ground                      true
% 3.10/0.95  --sup_to_prop_solver                    passive
% 3.10/0.95  --sup_prop_simpl_new                    true
% 3.10/0.95  --sup_prop_simpl_given                  true
% 3.10/0.95  --sup_fun_splitting                     false
% 3.10/0.95  --sup_smt_interval                      50000
% 3.10/0.95  
% 3.10/0.95  ------ Superposition Simplification Setup
% 3.10/0.95  
% 3.10/0.95  --sup_indices_passive                   []
% 3.10/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_full_bw                           [BwDemod]
% 3.10/0.95  --sup_immed_triv                        [TrivRules]
% 3.10/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_immed_bw_main                     []
% 3.10/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.95  
% 3.10/0.95  ------ Combination Options
% 3.10/0.95  
% 3.10/0.95  --comb_res_mult                         3
% 3.10/0.95  --comb_sup_mult                         2
% 3.10/0.95  --comb_inst_mult                        10
% 3.10/0.95  
% 3.10/0.95  ------ Debug Options
% 3.10/0.95  
% 3.10/0.95  --dbg_backtrace                         false
% 3.10/0.95  --dbg_dump_prop_clauses                 false
% 3.10/0.95  --dbg_dump_prop_clauses_file            -
% 3.10/0.95  --dbg_out_stat                          false
% 3.10/0.95  ------ Parsing...
% 3.10/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.95  ------ Proving...
% 3.10/0.95  ------ Problem Properties 
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  clauses                                 29
% 3.10/0.95  conjectures                             5
% 3.10/0.95  EPR                                     2
% 3.10/0.95  Horn                                    25
% 3.10/0.95  unary                                   8
% 3.10/0.95  binary                                  3
% 3.10/0.95  lits                                    90
% 3.10/0.95  lits eq                                 23
% 3.10/0.95  fd_pure                                 0
% 3.10/0.95  fd_pseudo                               0
% 3.10/0.95  fd_cond                                 3
% 3.10/0.95  fd_pseudo_cond                          0
% 3.10/0.95  AC symbols                              0
% 3.10/0.95  
% 3.10/0.95  ------ Schedule dynamic 5 is on 
% 3.10/0.95  
% 3.10/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  ------ 
% 3.10/0.95  Current options:
% 3.10/0.95  ------ 
% 3.10/0.95  
% 3.10/0.95  ------ Input Options
% 3.10/0.95  
% 3.10/0.95  --out_options                           all
% 3.10/0.95  --tptp_safe_out                         true
% 3.10/0.95  --problem_path                          ""
% 3.10/0.95  --include_path                          ""
% 3.10/0.95  --clausifier                            res/vclausify_rel
% 3.10/0.95  --clausifier_options                    --mode clausify
% 3.10/0.95  --stdin                                 false
% 3.10/0.95  --stats_out                             all
% 3.10/0.95  
% 3.10/0.95  ------ General Options
% 3.10/0.95  
% 3.10/0.95  --fof                                   false
% 3.10/0.95  --time_out_real                         305.
% 3.10/0.95  --time_out_virtual                      -1.
% 3.10/0.95  --symbol_type_check                     false
% 3.10/0.95  --clausify_out                          false
% 3.10/0.95  --sig_cnt_out                           false
% 3.10/0.95  --trig_cnt_out                          false
% 3.10/0.95  --trig_cnt_out_tolerance                1.
% 3.10/0.95  --trig_cnt_out_sk_spl                   false
% 3.10/0.95  --abstr_cl_out                          false
% 3.10/0.95  
% 3.10/0.95  ------ Global Options
% 3.10/0.95  
% 3.10/0.95  --schedule                              default
% 3.10/0.95  --add_important_lit                     false
% 3.10/0.95  --prop_solver_per_cl                    1000
% 3.10/0.95  --min_unsat_core                        false
% 3.10/0.95  --soft_assumptions                      false
% 3.10/0.95  --soft_lemma_size                       3
% 3.10/0.95  --prop_impl_unit_size                   0
% 3.10/0.95  --prop_impl_unit                        []
% 3.10/0.95  --share_sel_clauses                     true
% 3.10/0.95  --reset_solvers                         false
% 3.10/0.95  --bc_imp_inh                            [conj_cone]
% 3.10/0.95  --conj_cone_tolerance                   3.
% 3.10/0.95  --extra_neg_conj                        none
% 3.10/0.95  --large_theory_mode                     true
% 3.10/0.95  --prolific_symb_bound                   200
% 3.10/0.95  --lt_threshold                          2000
% 3.10/0.95  --clause_weak_htbl                      true
% 3.10/0.95  --gc_record_bc_elim                     false
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing Options
% 3.10/0.95  
% 3.10/0.95  --preprocessing_flag                    true
% 3.10/0.95  --time_out_prep_mult                    0.1
% 3.10/0.95  --splitting_mode                        input
% 3.10/0.95  --splitting_grd                         true
% 3.10/0.95  --splitting_cvd                         false
% 3.10/0.95  --splitting_cvd_svl                     false
% 3.10/0.95  --splitting_nvd                         32
% 3.10/0.95  --sub_typing                            true
% 3.10/0.95  --prep_gs_sim                           true
% 3.10/0.95  --prep_unflatten                        true
% 3.10/0.95  --prep_res_sim                          true
% 3.10/0.95  --prep_upred                            true
% 3.10/0.95  --prep_sem_filter                       exhaustive
% 3.10/0.95  --prep_sem_filter_out                   false
% 3.10/0.95  --pred_elim                             true
% 3.10/0.95  --res_sim_input                         true
% 3.10/0.95  --eq_ax_congr_red                       true
% 3.10/0.95  --pure_diseq_elim                       true
% 3.10/0.95  --brand_transform                       false
% 3.10/0.95  --non_eq_to_eq                          false
% 3.10/0.95  --prep_def_merge                        true
% 3.10/0.95  --prep_def_merge_prop_impl              false
% 3.10/0.95  --prep_def_merge_mbd                    true
% 3.10/0.95  --prep_def_merge_tr_red                 false
% 3.10/0.95  --prep_def_merge_tr_cl                  false
% 3.10/0.95  --smt_preprocessing                     true
% 3.10/0.95  --smt_ac_axioms                         fast
% 3.10/0.95  --preprocessed_out                      false
% 3.10/0.95  --preprocessed_stats                    false
% 3.10/0.95  
% 3.10/0.95  ------ Abstraction refinement Options
% 3.10/0.95  
% 3.10/0.95  --abstr_ref                             []
% 3.10/0.95  --abstr_ref_prep                        false
% 3.10/0.95  --abstr_ref_until_sat                   false
% 3.10/0.95  --abstr_ref_sig_restrict                funpre
% 3.10/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.95  --abstr_ref_under                       []
% 3.10/0.95  
% 3.10/0.95  ------ SAT Options
% 3.10/0.95  
% 3.10/0.95  --sat_mode                              false
% 3.10/0.95  --sat_fm_restart_options                ""
% 3.10/0.95  --sat_gr_def                            false
% 3.10/0.95  --sat_epr_types                         true
% 3.10/0.95  --sat_non_cyclic_types                  false
% 3.10/0.95  --sat_finite_models                     false
% 3.10/0.95  --sat_fm_lemmas                         false
% 3.10/0.95  --sat_fm_prep                           false
% 3.10/0.95  --sat_fm_uc_incr                        true
% 3.10/0.95  --sat_out_model                         small
% 3.10/0.95  --sat_out_clauses                       false
% 3.10/0.95  
% 3.10/0.95  ------ QBF Options
% 3.10/0.95  
% 3.10/0.95  --qbf_mode                              false
% 3.10/0.95  --qbf_elim_univ                         false
% 3.10/0.95  --qbf_dom_inst                          none
% 3.10/0.95  --qbf_dom_pre_inst                      false
% 3.10/0.95  --qbf_sk_in                             false
% 3.10/0.95  --qbf_pred_elim                         true
% 3.10/0.95  --qbf_split                             512
% 3.10/0.95  
% 3.10/0.95  ------ BMC1 Options
% 3.10/0.95  
% 3.10/0.95  --bmc1_incremental                      false
% 3.10/0.95  --bmc1_axioms                           reachable_all
% 3.10/0.95  --bmc1_min_bound                        0
% 3.10/0.95  --bmc1_max_bound                        -1
% 3.10/0.95  --bmc1_max_bound_default                -1
% 3.10/0.95  --bmc1_symbol_reachability              true
% 3.10/0.95  --bmc1_property_lemmas                  false
% 3.10/0.95  --bmc1_k_induction                      false
% 3.10/0.95  --bmc1_non_equiv_states                 false
% 3.10/0.95  --bmc1_deadlock                         false
% 3.10/0.95  --bmc1_ucm                              false
% 3.10/0.95  --bmc1_add_unsat_core                   none
% 3.10/0.95  --bmc1_unsat_core_children              false
% 3.10/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.95  --bmc1_out_stat                         full
% 3.10/0.95  --bmc1_ground_init                      false
% 3.10/0.95  --bmc1_pre_inst_next_state              false
% 3.10/0.95  --bmc1_pre_inst_state                   false
% 3.10/0.95  --bmc1_pre_inst_reach_state             false
% 3.10/0.95  --bmc1_out_unsat_core                   false
% 3.10/0.95  --bmc1_aig_witness_out                  false
% 3.10/0.95  --bmc1_verbose                          false
% 3.10/0.95  --bmc1_dump_clauses_tptp                false
% 3.10/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.95  --bmc1_dump_file                        -
% 3.10/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.95  --bmc1_ucm_extend_mode                  1
% 3.10/0.95  --bmc1_ucm_init_mode                    2
% 3.10/0.95  --bmc1_ucm_cone_mode                    none
% 3.10/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.95  --bmc1_ucm_relax_model                  4
% 3.10/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.95  --bmc1_ucm_layered_model                none
% 3.10/0.95  --bmc1_ucm_max_lemma_size               10
% 3.10/0.95  
% 3.10/0.95  ------ AIG Options
% 3.10/0.95  
% 3.10/0.95  --aig_mode                              false
% 3.10/0.95  
% 3.10/0.95  ------ Instantiation Options
% 3.10/0.95  
% 3.10/0.95  --instantiation_flag                    true
% 3.10/0.95  --inst_sos_flag                         false
% 3.10/0.95  --inst_sos_phase                        true
% 3.10/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.95  --inst_lit_sel_side                     none
% 3.10/0.95  --inst_solver_per_active                1400
% 3.10/0.95  --inst_solver_calls_frac                1.
% 3.10/0.95  --inst_passive_queue_type               priority_queues
% 3.10/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.95  --inst_passive_queues_freq              [25;2]
% 3.10/0.95  --inst_dismatching                      true
% 3.10/0.95  --inst_eager_unprocessed_to_passive     true
% 3.10/0.95  --inst_prop_sim_given                   true
% 3.10/0.95  --inst_prop_sim_new                     false
% 3.10/0.95  --inst_subs_new                         false
% 3.10/0.95  --inst_eq_res_simp                      false
% 3.10/0.95  --inst_subs_given                       false
% 3.10/0.95  --inst_orphan_elimination               true
% 3.10/0.95  --inst_learning_loop_flag               true
% 3.10/0.95  --inst_learning_start                   3000
% 3.10/0.95  --inst_learning_factor                  2
% 3.10/0.95  --inst_start_prop_sim_after_learn       3
% 3.10/0.95  --inst_sel_renew                        solver
% 3.10/0.95  --inst_lit_activity_flag                true
% 3.10/0.95  --inst_restr_to_given                   false
% 3.10/0.95  --inst_activity_threshold               500
% 3.10/0.95  --inst_out_proof                        true
% 3.10/0.95  
% 3.10/0.95  ------ Resolution Options
% 3.10/0.95  
% 3.10/0.95  --resolution_flag                       false
% 3.10/0.95  --res_lit_sel                           adaptive
% 3.10/0.95  --res_lit_sel_side                      none
% 3.10/0.95  --res_ordering                          kbo
% 3.10/0.95  --res_to_prop_solver                    active
% 3.10/0.95  --res_prop_simpl_new                    false
% 3.10/0.95  --res_prop_simpl_given                  true
% 3.10/0.95  --res_passive_queue_type                priority_queues
% 3.10/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.95  --res_passive_queues_freq               [15;5]
% 3.10/0.95  --res_forward_subs                      full
% 3.10/0.95  --res_backward_subs                     full
% 3.10/0.95  --res_forward_subs_resolution           true
% 3.10/0.95  --res_backward_subs_resolution          true
% 3.10/0.95  --res_orphan_elimination                true
% 3.10/0.95  --res_time_limit                        2.
% 3.10/0.95  --res_out_proof                         true
% 3.10/0.95  
% 3.10/0.95  ------ Superposition Options
% 3.10/0.95  
% 3.10/0.95  --superposition_flag                    true
% 3.10/0.95  --sup_passive_queue_type                priority_queues
% 3.10/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.95  --demod_completeness_check              fast
% 3.10/0.95  --demod_use_ground                      true
% 3.10/0.95  --sup_to_prop_solver                    passive
% 3.10/0.95  --sup_prop_simpl_new                    true
% 3.10/0.95  --sup_prop_simpl_given                  true
% 3.10/0.95  --sup_fun_splitting                     false
% 3.10/0.95  --sup_smt_interval                      50000
% 3.10/0.95  
% 3.10/0.95  ------ Superposition Simplification Setup
% 3.10/0.95  
% 3.10/0.95  --sup_indices_passive                   []
% 3.10/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_full_bw                           [BwDemod]
% 3.10/0.95  --sup_immed_triv                        [TrivRules]
% 3.10/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_immed_bw_main                     []
% 3.10/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.95  
% 3.10/0.95  ------ Combination Options
% 3.10/0.95  
% 3.10/0.95  --comb_res_mult                         3
% 3.10/0.95  --comb_sup_mult                         2
% 3.10/0.95  --comb_inst_mult                        10
% 3.10/0.95  
% 3.10/0.95  ------ Debug Options
% 3.10/0.95  
% 3.10/0.95  --dbg_backtrace                         false
% 3.10/0.95  --dbg_dump_prop_clauses                 false
% 3.10/0.95  --dbg_dump_prop_clauses_file            -
% 3.10/0.95  --dbg_out_stat                          false
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  ------ Proving...
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  % SZS status Theorem for theBenchmark.p
% 3.10/0.95  
% 3.10/0.95   Resolution empty clause
% 3.10/0.95  
% 3.10/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.95  
% 3.10/0.95  fof(f14,conjecture,(
% 3.10/0.95    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f15,negated_conjecture,(
% 3.10/0.95    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.10/0.95    inference(negated_conjecture,[],[f14])).
% 3.10/0.95  
% 3.10/0.95  fof(f36,plain,(
% 3.10/0.95    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.10/0.95    inference(ennf_transformation,[],[f15])).
% 3.10/0.95  
% 3.10/0.95  fof(f37,plain,(
% 3.10/0.95    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.10/0.95    inference(flattening,[],[f36])).
% 3.10/0.95  
% 3.10/0.95  fof(f41,plain,(
% 3.10/0.95    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.10/0.95    introduced(choice_axiom,[])).
% 3.10/0.95  
% 3.10/0.95  fof(f40,plain,(
% 3.10/0.95    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.10/0.95    introduced(choice_axiom,[])).
% 3.10/0.95  
% 3.10/0.95  fof(f39,plain,(
% 3.10/0.95    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.10/0.95    introduced(choice_axiom,[])).
% 3.10/0.95  
% 3.10/0.95  fof(f42,plain,(
% 3.10/0.95    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.10/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40,f39])).
% 3.10/0.95  
% 3.10/0.95  fof(f71,plain,(
% 3.10/0.95    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f11,axiom,(
% 3.10/0.95    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f31,plain,(
% 3.10/0.95    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.10/0.95    inference(ennf_transformation,[],[f11])).
% 3.10/0.95  
% 3.10/0.95  fof(f63,plain,(
% 3.10/0.95    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f31])).
% 3.10/0.95  
% 3.10/0.95  fof(f68,plain,(
% 3.10/0.95    l1_struct_0(sK1)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f66,plain,(
% 3.10/0.95    l1_struct_0(sK0)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f7,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f24,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(ennf_transformation,[],[f7])).
% 3.10/0.95  
% 3.10/0.95  fof(f52,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.95    inference(cnf_transformation,[],[f24])).
% 3.10/0.95  
% 3.10/0.95  fof(f72,plain,(
% 3.10/0.95    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f8,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f25,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(ennf_transformation,[],[f8])).
% 3.10/0.95  
% 3.10/0.95  fof(f26,plain,(
% 3.10/0.95    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(flattening,[],[f25])).
% 3.10/0.95  
% 3.10/0.95  fof(f38,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(nnf_transformation,[],[f26])).
% 3.10/0.95  
% 3.10/0.95  fof(f53,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.95    inference(cnf_transformation,[],[f38])).
% 3.10/0.95  
% 3.10/0.95  fof(f6,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f23,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(ennf_transformation,[],[f6])).
% 3.10/0.95  
% 3.10/0.95  fof(f51,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.95    inference(cnf_transformation,[],[f23])).
% 3.10/0.95  
% 3.10/0.95  fof(f70,plain,(
% 3.10/0.95    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f1,axiom,(
% 3.10/0.95    v1_xboole_0(k1_xboole_0)),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f43,plain,(
% 3.10/0.95    v1_xboole_0(k1_xboole_0)),
% 3.10/0.95    inference(cnf_transformation,[],[f1])).
% 3.10/0.95  
% 3.10/0.95  fof(f12,axiom,(
% 3.10/0.95    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f32,plain,(
% 3.10/0.95    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.10/0.95    inference(ennf_transformation,[],[f12])).
% 3.10/0.95  
% 3.10/0.95  fof(f33,plain,(
% 3.10/0.95    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.10/0.95    inference(flattening,[],[f32])).
% 3.10/0.95  
% 3.10/0.95  fof(f64,plain,(
% 3.10/0.95    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f33])).
% 3.10/0.95  
% 3.10/0.95  fof(f67,plain,(
% 3.10/0.95    ~v2_struct_0(sK1)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f13,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f34,plain,(
% 3.10/0.95    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.10/0.95    inference(ennf_transformation,[],[f13])).
% 3.10/0.95  
% 3.10/0.95  fof(f35,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.10/0.95    inference(flattening,[],[f34])).
% 3.10/0.95  
% 3.10/0.95  fof(f65,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f35])).
% 3.10/0.95  
% 3.10/0.95  fof(f69,plain,(
% 3.10/0.95    v1_funct_1(sK2)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f73,plain,(
% 3.10/0.95    v2_funct_1(sK2)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f9,axiom,(
% 3.10/0.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f27,plain,(
% 3.10/0.95    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.10/0.95    inference(ennf_transformation,[],[f9])).
% 3.10/0.95  
% 3.10/0.95  fof(f28,plain,(
% 3.10/0.95    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.10/0.95    inference(flattening,[],[f27])).
% 3.10/0.95  
% 3.10/0.95  fof(f59,plain,(
% 3.10/0.95    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f28])).
% 3.10/0.95  
% 3.10/0.95  fof(f74,plain,(
% 3.10/0.95    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.10/0.95    inference(cnf_transformation,[],[f42])).
% 3.10/0.95  
% 3.10/0.95  fof(f5,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f22,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.95    inference(ennf_transformation,[],[f5])).
% 3.10/0.95  
% 3.10/0.95  fof(f50,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.95    inference(cnf_transformation,[],[f22])).
% 3.10/0.95  
% 3.10/0.95  fof(f2,axiom,(
% 3.10/0.95    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f16,plain,(
% 3.10/0.95    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/0.95    inference(ennf_transformation,[],[f2])).
% 3.10/0.95  
% 3.10/0.95  fof(f17,plain,(
% 3.10/0.95    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/0.95    inference(flattening,[],[f16])).
% 3.10/0.95  
% 3.10/0.95  fof(f46,plain,(
% 3.10/0.95    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f17])).
% 3.10/0.95  
% 3.10/0.95  fof(f45,plain,(
% 3.10/0.95    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f17])).
% 3.10/0.95  
% 3.10/0.95  fof(f10,axiom,(
% 3.10/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f29,plain,(
% 3.10/0.95    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.10/0.95    inference(ennf_transformation,[],[f10])).
% 3.10/0.95  
% 3.10/0.95  fof(f30,plain,(
% 3.10/0.95    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.10/0.95    inference(flattening,[],[f29])).
% 3.10/0.95  
% 3.10/0.95  fof(f62,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f30])).
% 3.10/0.95  
% 3.10/0.95  fof(f61,plain,(
% 3.10/0.95    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f30])).
% 3.10/0.95  
% 3.10/0.95  fof(f3,axiom,(
% 3.10/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f18,plain,(
% 3.10/0.95    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/0.95    inference(ennf_transformation,[],[f3])).
% 3.10/0.95  
% 3.10/0.95  fof(f19,plain,(
% 3.10/0.95    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/0.95    inference(flattening,[],[f18])).
% 3.10/0.95  
% 3.10/0.95  fof(f48,plain,(
% 3.10/0.95    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f19])).
% 3.10/0.95  
% 3.10/0.95  fof(f4,axiom,(
% 3.10/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.10/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.95  
% 3.10/0.95  fof(f20,plain,(
% 3.10/0.95    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/0.95    inference(ennf_transformation,[],[f4])).
% 3.10/0.95  
% 3.10/0.95  fof(f21,plain,(
% 3.10/0.95    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/0.95    inference(flattening,[],[f20])).
% 3.10/0.95  
% 3.10/0.95  fof(f49,plain,(
% 3.10/0.95    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/0.95    inference(cnf_transformation,[],[f21])).
% 3.10/0.95  
% 3.10/0.95  cnf(c_26,negated_conjecture,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.10/0.95      inference(cnf_transformation,[],[f71]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1060,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_20,plain,
% 3.10/0.95      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f63]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_29,negated_conjecture,
% 3.10/0.95      ( l1_struct_0(sK1) ),
% 3.10/0.95      inference(cnf_transformation,[],[f68]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_383,plain,
% 3.10/0.95      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.10/0.95      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_384,plain,
% 3.10/0.95      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.10/0.95      inference(unflattening,[status(thm)],[c_383]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_31,negated_conjecture,
% 3.10/0.95      ( l1_struct_0(sK0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f66]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_388,plain,
% 3.10/0.95      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.10/0.95      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_389,plain,
% 3.10/0.95      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.10/0.95      inference(unflattening,[status(thm)],[c_388]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1096,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1060,c_384,c_389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_9,plain,
% 3.10/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f52]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1071,plain,
% 3.10/0.95      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1519,plain,
% 3.10/0.95      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1096,c_1071]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_25,negated_conjecture,
% 3.10/0.95      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.10/0.95      inference(cnf_transformation,[],[f72]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1093,plain,
% 3.10/0.95      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_25,c_384,c_389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1685,plain,
% 3.10/0.95      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_1519,c_1093]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1802,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_1685,c_1096]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_15,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | k1_relset_1(X1,X2,X0) = X1
% 3.10/0.95      | k1_xboole_0 = X2 ),
% 3.10/0.95      inference(cnf_transformation,[],[f53]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1065,plain,
% 3.10/0.95      ( k1_relset_1(X0,X1,X2) = X0
% 3.10/0.95      | k1_xboole_0 = X1
% 3.10/0.95      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3770,plain,
% 3.10/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 3.10/0.95      | k2_relat_1(sK2) = k1_xboole_0
% 3.10/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1802,c_1065]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_8,plain,
% 3.10/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f51]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1072,plain,
% 3.10/0.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1523,plain,
% 3.10/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1096,c_1072]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1922,plain,
% 3.10/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1523,c_1685]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3771,plain,
% 3.10/0.95      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.10/0.95      | k2_relat_1(sK2) = k1_xboole_0
% 3.10/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_3770,c_1922]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_27,negated_conjecture,
% 3.10/0.95      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.10/0.95      inference(cnf_transformation,[],[f70]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1059,plain,
% 3.10/0.95      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1090,plain,
% 3.10/0.95      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1059,c_384,c_389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1803,plain,
% 3.10/0.95      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_1685,c_1090]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_0,plain,
% 3.10/0.95      ( v1_xboole_0(k1_xboole_0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_21,plain,
% 3.10/0.95      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.10/0.95      inference(cnf_transformation,[],[f64]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_356,plain,
% 3.10/0.95      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 ),
% 3.10/0.95      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_30,negated_conjecture,
% 3.10/0.95      ( ~ v2_struct_0(sK1) ),
% 3.10/0.95      inference(cnf_transformation,[],[f67]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_374,plain,
% 3.10/0.95      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 3.10/0.95      inference(resolution_lifted,[status(thm)],[c_356,c_30]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_375,plain,
% 3.10/0.95      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 3.10/0.95      inference(unflattening,[status(thm)],[c_374]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_377,plain,
% 3.10/0.95      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.10/0.95      inference(global_propositional_subsumption,[status(thm)],[c_375,c_29]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1805,plain,
% 3.10/0.95      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_1685,c_377]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3951,plain,
% 3.10/0.95      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_3771,c_1803,c_1805]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1800,plain,
% 3.10/0.95      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_1685,c_1519]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_22,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.10/0.95      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.10/0.95      inference(cnf_transformation,[],[f65]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1062,plain,
% 3.10/0.95      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.10/0.95      | k2_relset_1(X0,X1,X2) != X1
% 3.10/0.95      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.10/0.95      | v1_funct_1(X2) != iProver_top
% 3.10/0.95      | v2_funct_1(X2) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2212,plain,
% 3.10/0.95      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.10/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1800,c_1062]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_28,negated_conjecture,
% 3.10/0.95      ( v1_funct_1(sK2) ),
% 3.10/0.95      inference(cnf_transformation,[],[f69]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_35,plain,
% 3.10/0.95      ( v1_funct_1(sK2) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_24,negated_conjecture,
% 3.10/0.95      ( v2_funct_1(sK2) ),
% 3.10/0.95      inference(cnf_transformation,[],[f73]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_38,plain,
% 3.10/0.95      ( v2_funct_1(sK2) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2612,plain,
% 3.10/0.95      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_2212,c_35,c_38,c_1802,c_1803]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_16,plain,
% 3.10/0.95      ( r2_funct_2(X0,X1,X2,X2)
% 3.10/0.95      | ~ v1_funct_2(X2,X0,X1)
% 3.10/0.95      | ~ v1_funct_2(X3,X0,X1)
% 3.10/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.95      | ~ v1_funct_1(X3)
% 3.10/0.95      | ~ v1_funct_1(X2) ),
% 3.10/0.95      inference(cnf_transformation,[],[f59]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_23,negated_conjecture,
% 3.10/0.95      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.10/0.95      inference(cnf_transformation,[],[f74]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_395,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.95      | ~ v1_funct_2(X3,X1,X2)
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | ~ v1_funct_1(X3)
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.10/0.95      | u1_struct_0(sK1) != X2
% 3.10/0.95      | u1_struct_0(sK0) != X1
% 3.10/0.95      | sK2 != X0 ),
% 3.10/0.95      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_396,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.10/0.95      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.10/0.95      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.10/0.95      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.10/0.95      inference(unflattening,[status(thm)],[c_395]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_596,plain,
% 3.10/0.95      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.10/0.95      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.10/0.95      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.10/0.95      | sP0_iProver_split
% 3.10/0.95      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.10/0.95      inference(splitting,
% 3.10/0.95                [splitting(split),new_symbols(definition,[])],
% 3.10/0.95                [c_396]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1055,plain,
% 3.10/0.95      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.10/0.95      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.10/0.95      | sP0_iProver_split = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1254,plain,
% 3.10/0.95      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.10/0.95      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.10/0.95      | sP0_iProver_split = iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1055,c_384,c_389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_595,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ sP0_iProver_split ),
% 3.10/0.95      inference(splitting,
% 3.10/0.95                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.10/0.95                [c_396]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1056,plain,
% 3.10/0.95      ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.10/0.95      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_funct_1(X0) != iProver_top
% 3.10/0.95      | sP0_iProver_split != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1209,plain,
% 3.10/0.95      ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.10/0.95      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_funct_1(X0) != iProver_top
% 3.10/0.95      | sP0_iProver_split != iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1056,c_384,c_389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1260,plain,
% 3.10/0.95      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.10/0.95      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.10/0.95      inference(forward_subsumption_resolution,[status(thm)],[c_1254,c_1209]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2489,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.10/0.95      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_1260,c_1685]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2615,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.10/0.95      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_2612,c_2489]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3955,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.10/0.95      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_3951,c_2615]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_37,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_7,plain,
% 3.10/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f50]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1326,plain,
% 3.10/0.95      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.10/0.95      | v1_relat_1(sK2) ),
% 3.10/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1327,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.10/0.95      | v1_relat_1(sK2) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1,plain,
% 3.10/0.95      ( ~ v1_relat_1(X0)
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | v2_funct_1(k2_funct_1(X0)) ),
% 3.10/0.95      inference(cnf_transformation,[],[f46]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1390,plain,
% 3.10/0.95      ( ~ v1_relat_1(sK2)
% 3.10/0.95      | ~ v1_funct_1(sK2)
% 3.10/0.95      | v2_funct_1(k2_funct_1(sK2))
% 3.10/0.95      | ~ v2_funct_1(sK2) ),
% 3.10/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1391,plain,
% 3.10/0.95      ( v1_relat_1(sK2) != iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2,plain,
% 3.10/0.95      ( ~ v1_relat_1(X0)
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | v1_funct_1(k2_funct_1(X0))
% 3.10/0.95      | ~ v2_funct_1(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f45]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1389,plain,
% 3.10/0.95      ( ~ v1_relat_1(sK2)
% 3.10/0.95      | v1_funct_1(k2_funct_1(sK2))
% 3.10/0.95      | ~ v1_funct_1(sK2)
% 3.10/0.95      | ~ v2_funct_1(sK2) ),
% 3.10/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1393,plain,
% 3.10/0.95      ( v1_relat_1(sK2) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_17,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.10/0.95      inference(cnf_transformation,[],[f62]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1064,plain,
% 3.10/0.95      ( k2_relset_1(X0,X1,X2) != X1
% 3.10/0.95      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.10/0.95      | v1_funct_1(X2) != iProver_top
% 3.10/0.95      | v2_funct_1(X2) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3743,plain,
% 3.10/0.95      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.10/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1800,c_1064]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3880,plain,
% 3.10/0.95      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_3743,c_35,c_38,c_1802,c_1803]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3954,plain,
% 3.10/0.95      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_3951,c_3880]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_18,plain,
% 3.10/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.95      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.10/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.10/0.95      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1063,plain,
% 3.10/0.95      ( k2_relset_1(X0,X1,X2) != X1
% 3.10/0.95      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.10/0.95      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 3.10/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.10/0.95      | v1_funct_1(X2) != iProver_top
% 3.10/0.95      | v2_funct_1(X2) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2624,plain,
% 3.10/0.95      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 3.10/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1800,c_1063]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3173,plain,
% 3.10/0.95      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_2624,c_35,c_38,c_1802,c_1803]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3956,plain,
% 3.10/0.95      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_3951,c_3173]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3889,plain,
% 3.10/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_3880,c_1071]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1073,plain,
% 3.10/0.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/0.95      | v1_relat_1(X0) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1417,plain,
% 3.10/0.95      ( v1_relat_1(sK2) = iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1096,c_1073]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_4,plain,
% 3.10/0.95      ( ~ v1_relat_1(X0)
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.10/0.95      inference(cnf_transformation,[],[f48]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1076,plain,
% 3.10/0.95      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.10/0.95      | v1_relat_1(X0) != iProver_top
% 3.10/0.95      | v1_funct_1(X0) != iProver_top
% 3.10/0.95      | v2_funct_1(X0) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2781,plain,
% 3.10/0.95      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1417,c_1076]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1385,plain,
% 3.10/0.95      ( ~ v1_relat_1(sK2)
% 3.10/0.95      | ~ v1_funct_1(sK2)
% 3.10/0.95      | ~ v2_funct_1(sK2)
% 3.10/0.95      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(instantiation,[status(thm)],[c_4]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3034,plain,
% 3.10/0.95      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_2781,c_28,c_26,c_24,c_1326,c_1385]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3891,plain,
% 3.10/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_3889,c_3034]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_4883,plain,
% 3.10/0.95      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_3891,c_3951]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_4887,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.10/0.95      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/0.95      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_4883,c_1062]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_6,plain,
% 3.10/0.95      ( ~ v1_relat_1(X0)
% 3.10/0.95      | ~ v1_funct_1(X0)
% 3.10/0.95      | ~ v2_funct_1(X0)
% 3.10/0.95      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.10/0.95      inference(cnf_transformation,[],[f49]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1074,plain,
% 3.10/0.95      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.10/0.95      | v1_relat_1(X0) != iProver_top
% 3.10/0.95      | v1_funct_1(X0) != iProver_top
% 3.10/0.95      | v2_funct_1(X0) != iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2018,plain,
% 3.10/0.95      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top
% 3.10/0.95      | v2_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(superposition,[status(thm)],[c_1417,c_1074]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1386,plain,
% 3.10/0.95      ( ~ v1_relat_1(sK2)
% 3.10/0.95      | ~ v1_funct_1(sK2)
% 3.10/0.95      | ~ v2_funct_1(sK2)
% 3.10/0.95      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.10/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_2496,plain,
% 3.10/0.95      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_2018,c_28,c_26,c_24,c_1326,c_1386]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_4893,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.10/0.95      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/0.95      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_4887,c_2496]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_5145,plain,
% 3.10/0.95      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_3955,c_35,c_37,c_38,c_1327,c_1391,c_1393,c_3954,c_3956,
% 3.10/0.95                 c_4893]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_4927,plain,
% 3.10/0.95      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.10/0.95      inference(global_propositional_subsumption,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_4893,c_35,c_37,c_38,c_1327,c_1391,c_1393,c_3954,c_3956]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_5149,plain,
% 3.10/0.95      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.10/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.10/0.95      | v1_funct_1(sK2) != iProver_top ),
% 3.10/0.95      inference(light_normalisation,[status(thm)],[c_5145,c_4927]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_1058,plain,
% 3.10/0.95      ( v1_funct_1(sK2) = iProver_top ),
% 3.10/0.95      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3958,plain,
% 3.10/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_3951,c_1802]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_3961,plain,
% 3.10/0.95      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.10/0.95      inference(demodulation,[status(thm)],[c_3951,c_1803]) ).
% 3.10/0.95  
% 3.10/0.95  cnf(c_5153,plain,
% 3.10/0.95      ( $false ),
% 3.10/0.95      inference(forward_subsumption_resolution,
% 3.10/0.95                [status(thm)],
% 3.10/0.95                [c_5149,c_1058,c_3958,c_3961]) ).
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.95  
% 3.10/0.95  ------                               Statistics
% 3.10/0.95  
% 3.10/0.95  ------ General
% 3.10/0.95  
% 3.10/0.95  abstr_ref_over_cycles:                  0
% 3.10/0.95  abstr_ref_under_cycles:                 0
% 3.10/0.95  gc_basic_clause_elim:                   0
% 3.10/0.95  forced_gc_time:                         0
% 3.10/0.95  parsing_time:                           0.01
% 3.10/0.95  unif_index_cands_time:                  0.
% 3.10/0.95  unif_index_add_time:                    0.
% 3.10/0.95  orderings_time:                         0.
% 3.10/0.95  out_proof_time:                         0.019
% 3.10/0.95  total_time:                             0.222
% 3.10/0.95  num_of_symbols:                         55
% 3.10/0.95  num_of_terms:                           4074
% 3.10/0.95  
% 3.10/0.95  ------ Preprocessing
% 3.10/0.95  
% 3.10/0.95  num_of_splits:                          1
% 3.10/0.95  num_of_split_atoms:                     1
% 3.10/0.95  num_of_reused_defs:                     0
% 3.10/0.95  num_eq_ax_congr_red:                    6
% 3.10/0.95  num_of_sem_filtered_clauses:            1
% 3.10/0.95  num_of_subtypes:                        0
% 3.10/0.95  monotx_restored_types:                  0
% 3.10/0.95  sat_num_of_epr_types:                   0
% 3.10/0.95  sat_num_of_non_cyclic_types:            0
% 3.10/0.95  sat_guarded_non_collapsed_types:        0
% 3.10/0.95  num_pure_diseq_elim:                    0
% 3.10/0.95  simp_replaced_by:                       0
% 3.10/0.95  res_preprocessed:                       153
% 3.10/0.95  prep_upred:                             0
% 3.10/0.95  prep_unflattend:                        6
% 3.10/0.95  smt_new_axioms:                         0
% 3.10/0.95  pred_elim_cands:                        5
% 3.10/0.95  pred_elim:                              4
% 3.10/0.95  pred_elim_cl:                           4
% 3.10/0.95  pred_elim_cycles:                       6
% 3.10/0.95  merged_defs:                            0
% 3.10/0.95  merged_defs_ncl:                        0
% 3.10/0.95  bin_hyper_res:                          0
% 3.10/0.95  prep_cycles:                            4
% 3.10/0.95  pred_elim_time:                         0.003
% 3.10/0.95  splitting_time:                         0.
% 3.10/0.95  sem_filter_time:                        0.
% 3.10/0.95  monotx_time:                            0.
% 3.10/0.95  subtype_inf_time:                       0.
% 3.10/0.95  
% 3.10/0.95  ------ Problem properties
% 3.10/0.95  
% 3.10/0.95  clauses:                                29
% 3.10/0.95  conjectures:                            5
% 3.10/0.95  epr:                                    2
% 3.10/0.95  horn:                                   25
% 3.10/0.95  ground:                                 9
% 3.10/0.95  unary:                                  8
% 3.10/0.95  binary:                                 3
% 3.10/0.95  lits:                                   90
% 3.10/0.95  lits_eq:                                23
% 3.10/0.95  fd_pure:                                0
% 3.10/0.95  fd_pseudo:                              0
% 3.10/0.95  fd_cond:                                3
% 3.10/0.95  fd_pseudo_cond:                         0
% 3.10/0.95  ac_symbols:                             0
% 3.10/0.95  
% 3.10/0.95  ------ Propositional Solver
% 3.10/0.95  
% 3.10/0.95  prop_solver_calls:                      28
% 3.10/0.95  prop_fast_solver_calls:                 1217
% 3.10/0.95  smt_solver_calls:                       0
% 3.10/0.95  smt_fast_solver_calls:                  0
% 3.10/0.95  prop_num_of_clauses:                    1508
% 3.10/0.95  prop_preprocess_simplified:             5503
% 3.10/0.95  prop_fo_subsumed:                       55
% 3.10/0.95  prop_solver_time:                       0.
% 3.10/0.95  smt_solver_time:                        0.
% 3.10/0.95  smt_fast_solver_time:                   0.
% 3.10/0.95  prop_fast_solver_time:                  0.
% 3.10/0.95  prop_unsat_core_time:                   0.
% 3.10/0.95  
% 3.10/0.95  ------ QBF
% 3.10/0.95  
% 3.10/0.95  qbf_q_res:                              0
% 3.10/0.95  qbf_num_tautologies:                    0
% 3.10/0.95  qbf_prep_cycles:                        0
% 3.10/0.95  
% 3.10/0.95  ------ BMC1
% 3.10/0.95  
% 3.10/0.95  bmc1_current_bound:                     -1
% 3.10/0.95  bmc1_last_solved_bound:                 -1
% 3.10/0.95  bmc1_unsat_core_size:                   -1
% 3.10/0.95  bmc1_unsat_core_parents_size:           -1
% 3.10/0.95  bmc1_merge_next_fun:                    0
% 3.10/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.95  
% 3.10/0.95  ------ Instantiation
% 3.10/0.95  
% 3.10/0.95  inst_num_of_clauses:                    554
% 3.10/0.95  inst_num_in_passive:                    59
% 3.10/0.95  inst_num_in_active:                     344
% 3.10/0.95  inst_num_in_unprocessed:                151
% 3.10/0.95  inst_num_of_loops:                      360
% 3.10/0.95  inst_num_of_learning_restarts:          0
% 3.10/0.95  inst_num_moves_active_passive:          12
% 3.10/0.95  inst_lit_activity:                      0
% 3.10/0.95  inst_lit_activity_moves:                0
% 3.10/0.95  inst_num_tautologies:                   0
% 3.10/0.95  inst_num_prop_implied:                  0
% 3.10/0.95  inst_num_existing_simplified:           0
% 3.10/0.95  inst_num_eq_res_simplified:             0
% 3.10/0.95  inst_num_child_elim:                    0
% 3.10/0.95  inst_num_of_dismatching_blockings:      68
% 3.10/0.95  inst_num_of_non_proper_insts:           417
% 3.10/0.95  inst_num_of_duplicates:                 0
% 3.10/0.95  inst_inst_num_from_inst_to_res:         0
% 3.10/0.95  inst_dismatching_checking_time:         0.
% 3.10/0.95  
% 3.10/0.95  ------ Resolution
% 3.10/0.95  
% 3.10/0.95  res_num_of_clauses:                     0
% 3.10/0.95  res_num_in_passive:                     0
% 3.10/0.95  res_num_in_active:                      0
% 3.10/0.95  res_num_of_loops:                       157
% 3.10/0.95  res_forward_subset_subsumed:            38
% 3.10/0.95  res_backward_subset_subsumed:           2
% 3.10/0.95  res_forward_subsumed:                   0
% 3.10/0.95  res_backward_subsumed:                  0
% 3.10/0.95  res_forward_subsumption_resolution:     0
% 3.10/0.95  res_backward_subsumption_resolution:    0
% 3.10/0.95  res_clause_to_clause_subsumption:       222
% 3.10/0.95  res_orphan_elimination:                 0
% 3.10/0.95  res_tautology_del:                      46
% 3.10/0.95  res_num_eq_res_simplified:              0
% 3.10/0.95  res_num_sel_changes:                    0
% 3.10/0.95  res_moves_from_active_to_pass:          0
% 3.10/0.95  
% 3.10/0.95  ------ Superposition
% 3.10/0.95  
% 3.10/0.95  sup_time_total:                         0.
% 3.10/0.95  sup_time_generating:                    0.
% 3.10/0.95  sup_time_sim_full:                      0.
% 3.10/0.95  sup_time_sim_immed:                     0.
% 3.10/0.95  
% 3.10/0.95  sup_num_of_clauses:                     56
% 3.10/0.95  sup_num_in_active:                      53
% 3.10/0.95  sup_num_in_passive:                     3
% 3.10/0.95  sup_num_of_loops:                       70
% 3.10/0.95  sup_fw_superposition:                   39
% 3.10/0.95  sup_bw_superposition:                   40
% 3.10/0.95  sup_immediate_simplified:               44
% 3.10/0.95  sup_given_eliminated:                   0
% 3.10/0.95  comparisons_done:                       0
% 3.10/0.95  comparisons_avoided:                    0
% 3.10/0.95  
% 3.10/0.95  ------ Simplifications
% 3.10/0.95  
% 3.10/0.95  
% 3.10/0.95  sim_fw_subset_subsumed:                 12
% 3.10/0.95  sim_bw_subset_subsumed:                 0
% 3.10/0.95  sim_fw_subsumed:                        3
% 3.10/0.95  sim_bw_subsumed:                        0
% 3.10/0.95  sim_fw_subsumption_res:                 4
% 3.10/0.95  sim_bw_subsumption_res:                 0
% 3.10/0.95  sim_tautology_del:                      0
% 3.10/0.95  sim_eq_tautology_del:                   25
% 3.10/0.95  sim_eq_res_simp:                        0
% 3.10/0.95  sim_fw_demodulated:                     0
% 3.10/0.95  sim_bw_demodulated:                     17
% 3.10/0.95  sim_light_normalised:                   42
% 3.10/0.95  sim_joinable_taut:                      0
% 3.10/0.95  sim_joinable_simp:                      0
% 3.10/0.95  sim_ac_normalised:                      0
% 3.10/0.95  sim_smt_subsumption:                    0
% 3.10/0.95  
%------------------------------------------------------------------------------
