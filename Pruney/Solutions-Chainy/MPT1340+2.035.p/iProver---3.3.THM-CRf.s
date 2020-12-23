%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:28 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  216 (5550 expanded)
%              Number of clauses        :  138 (1537 expanded)
%              Number of leaves         :   19 (1642 expanded)
%              Depth                    :   30
%              Number of atoms          :  774 (36073 expanded)
%              Number of equality atoms :  341 (6228 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
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

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f86,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_444,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_445,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_449,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_450,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1216,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1176,c_445,c_450])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1192,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1650,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1216,c_1192])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1213,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_31,c_445,c_450])).

cnf(c_1824,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1650,c_1213])).

cnf(c_1877,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1824,c_1216])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1183,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4723,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1877,c_1183])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1190,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2468,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1877,c_1190])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1191,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2470,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1877,c_1191])).

cnf(c_2477,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_2468,c_2470])).

cnf(c_4734,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4723,c_2477])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1175,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1210,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1175,c_445,c_450])).

cnf(c_1878,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1824,c_1210])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_417,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_435,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_36])).

cnf(c_436,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_35])).

cnf(c_1880,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1824,c_438])).

cnf(c_5886,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_1878,c_1880])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1535,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1193])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4722,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1183])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_56,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5662,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4722,c_56])).

cnf(c_5663,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5662])).

cnf(c_5673,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_5663])).

cnf(c_1875,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1824,c_1650])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1182,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3741,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1182])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4323,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3741,c_41,c_44,c_1877,c_1878])).

cnf(c_4328,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4323,c_1193])).

cnf(c_2331,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1192])).

cnf(c_4358,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4328,c_2331])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1195,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3988,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1195])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1538,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4172,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3988,c_34,c_32,c_30,c_1459,c_1538])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1196,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4136,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1196])).

cnf(c_1541,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4192,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4136,c_34,c_32,c_30,c_1459,c_1541])).

cnf(c_4366,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4358,c_4172,c_4192])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_217,plain,
    ( ~ v2_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_7,c_2])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1530,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1173])).

cnf(c_4675,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_41,c_44,c_1530])).

cnf(c_4678,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_1182])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1194,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2814,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1194])).

cnf(c_1537,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3076,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_34,c_32,c_30,c_1459,c_1537])).

cnf(c_4708,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4678,c_3076])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1460,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_1539,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1560,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_5206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4708,c_41,c_43,c_1460,c_1560])).

cnf(c_5214,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_5206,c_1190])).

cnf(c_2330,plain,
    ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1191])).

cnf(c_3496,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_2330])).

cnf(c_1730,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4160,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_34,c_32,c_1459,c_1539,c_1730])).

cnf(c_5222,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_5214,c_4160])).

cnf(c_5686,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5673,c_5222])).

cnf(c_1540,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1558,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_5213,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5206,c_1183])).

cnf(c_5224,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5213,c_5222])).

cnf(c_5876,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5686,c_41,c_43,c_1460,c_1558,c_1880,c_5224])).

cnf(c_5888,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5886,c_5876])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1178,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2067,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1178])).

cnf(c_2600,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_41,c_44,c_1877,c_1878])).

cnf(c_18,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_29,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_459,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_1172,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1385,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1172,c_445,c_450])).

cnf(c_1876,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1824,c_1385])).

cnf(c_2603,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2600,c_1876])).

cnf(c_5896,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5888,c_2603])).

cnf(c_4680,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_1178])).

cnf(c_4686,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4680,c_3076])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1545,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1546,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_1731,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1510,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1756,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_1757,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1756])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1515,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1761,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_1762,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_5202,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4686,c_34,c_41,c_32,c_43,c_44,c_1459,c_1460,c_1530,c_1546,c_1558,c_1539,c_1560,c_1731,c_1757,c_1762])).

cnf(c_5910,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5896,c_5202])).

cnf(c_5911,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5910])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5911,c_1560,c_1558,c_1460,c_43,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.35/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/1.00  
% 3.35/1.00  ------  iProver source info
% 3.35/1.00  
% 3.35/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.35/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/1.00  git: non_committed_changes: false
% 3.35/1.00  git: last_make_outside_of_git: false
% 3.35/1.00  
% 3.35/1.00  ------ 
% 3.35/1.00  
% 3.35/1.00  ------ Input Options
% 3.35/1.00  
% 3.35/1.00  --out_options                           all
% 3.35/1.00  --tptp_safe_out                         true
% 3.35/1.00  --problem_path                          ""
% 3.35/1.00  --include_path                          ""
% 3.35/1.00  --clausifier                            res/vclausify_rel
% 3.35/1.00  --clausifier_options                    --mode clausify
% 3.35/1.00  --stdin                                 false
% 3.35/1.00  --stats_out                             all
% 3.35/1.00  
% 3.35/1.00  ------ General Options
% 3.35/1.00  
% 3.35/1.00  --fof                                   false
% 3.35/1.00  --time_out_real                         305.
% 3.35/1.00  --time_out_virtual                      -1.
% 3.35/1.00  --symbol_type_check                     false
% 3.35/1.00  --clausify_out                          false
% 3.35/1.00  --sig_cnt_out                           false
% 3.35/1.00  --trig_cnt_out                          false
% 3.35/1.00  --trig_cnt_out_tolerance                1.
% 3.35/1.00  --trig_cnt_out_sk_spl                   false
% 3.35/1.00  --abstr_cl_out                          false
% 3.35/1.00  
% 3.35/1.00  ------ Global Options
% 3.35/1.00  
% 3.35/1.00  --schedule                              default
% 3.35/1.00  --add_important_lit                     false
% 3.35/1.00  --prop_solver_per_cl                    1000
% 3.35/1.00  --min_unsat_core                        false
% 3.35/1.00  --soft_assumptions                      false
% 3.35/1.00  --soft_lemma_size                       3
% 3.35/1.00  --prop_impl_unit_size                   0
% 3.35/1.00  --prop_impl_unit                        []
% 3.35/1.00  --share_sel_clauses                     true
% 3.35/1.00  --reset_solvers                         false
% 3.35/1.00  --bc_imp_inh                            [conj_cone]
% 3.35/1.00  --conj_cone_tolerance                   3.
% 3.35/1.00  --extra_neg_conj                        none
% 3.35/1.00  --large_theory_mode                     true
% 3.35/1.00  --prolific_symb_bound                   200
% 3.35/1.00  --lt_threshold                          2000
% 3.35/1.00  --clause_weak_htbl                      true
% 3.35/1.00  --gc_record_bc_elim                     false
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing Options
% 3.35/1.00  
% 3.35/1.00  --preprocessing_flag                    true
% 3.35/1.00  --time_out_prep_mult                    0.1
% 3.35/1.00  --splitting_mode                        input
% 3.35/1.00  --splitting_grd                         true
% 3.35/1.00  --splitting_cvd                         false
% 3.35/1.00  --splitting_cvd_svl                     false
% 3.35/1.00  --splitting_nvd                         32
% 3.35/1.00  --sub_typing                            true
% 3.35/1.00  --prep_gs_sim                           true
% 3.35/1.00  --prep_unflatten                        true
% 3.35/1.00  --prep_res_sim                          true
% 3.35/1.00  --prep_upred                            true
% 3.35/1.00  --prep_sem_filter                       exhaustive
% 3.35/1.00  --prep_sem_filter_out                   false
% 3.35/1.00  --pred_elim                             true
% 3.35/1.00  --res_sim_input                         true
% 3.35/1.00  --eq_ax_congr_red                       true
% 3.35/1.00  --pure_diseq_elim                       true
% 3.35/1.00  --brand_transform                       false
% 3.35/1.00  --non_eq_to_eq                          false
% 3.35/1.00  --prep_def_merge                        true
% 3.35/1.00  --prep_def_merge_prop_impl              false
% 3.35/1.00  --prep_def_merge_mbd                    true
% 3.35/1.00  --prep_def_merge_tr_red                 false
% 3.35/1.00  --prep_def_merge_tr_cl                  false
% 3.35/1.00  --smt_preprocessing                     true
% 3.35/1.00  --smt_ac_axioms                         fast
% 3.35/1.00  --preprocessed_out                      false
% 3.35/1.00  --preprocessed_stats                    false
% 3.35/1.00  
% 3.35/1.00  ------ Abstraction refinement Options
% 3.35/1.00  
% 3.35/1.00  --abstr_ref                             []
% 3.35/1.00  --abstr_ref_prep                        false
% 3.35/1.00  --abstr_ref_until_sat                   false
% 3.35/1.00  --abstr_ref_sig_restrict                funpre
% 3.35/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/1.00  --abstr_ref_under                       []
% 3.35/1.00  
% 3.35/1.00  ------ SAT Options
% 3.35/1.00  
% 3.35/1.00  --sat_mode                              false
% 3.35/1.00  --sat_fm_restart_options                ""
% 3.35/1.00  --sat_gr_def                            false
% 3.35/1.00  --sat_epr_types                         true
% 3.35/1.00  --sat_non_cyclic_types                  false
% 3.35/1.00  --sat_finite_models                     false
% 3.35/1.00  --sat_fm_lemmas                         false
% 3.35/1.00  --sat_fm_prep                           false
% 3.35/1.00  --sat_fm_uc_incr                        true
% 3.35/1.00  --sat_out_model                         small
% 3.35/1.00  --sat_out_clauses                       false
% 3.35/1.00  
% 3.35/1.00  ------ QBF Options
% 3.35/1.00  
% 3.35/1.00  --qbf_mode                              false
% 3.35/1.00  --qbf_elim_univ                         false
% 3.35/1.00  --qbf_dom_inst                          none
% 3.35/1.00  --qbf_dom_pre_inst                      false
% 3.35/1.00  --qbf_sk_in                             false
% 3.35/1.00  --qbf_pred_elim                         true
% 3.35/1.00  --qbf_split                             512
% 3.35/1.00  
% 3.35/1.00  ------ BMC1 Options
% 3.35/1.00  
% 3.35/1.00  --bmc1_incremental                      false
% 3.35/1.00  --bmc1_axioms                           reachable_all
% 3.35/1.00  --bmc1_min_bound                        0
% 3.35/1.00  --bmc1_max_bound                        -1
% 3.35/1.00  --bmc1_max_bound_default                -1
% 3.35/1.00  --bmc1_symbol_reachability              true
% 3.35/1.00  --bmc1_property_lemmas                  false
% 3.35/1.00  --bmc1_k_induction                      false
% 3.35/1.00  --bmc1_non_equiv_states                 false
% 3.35/1.00  --bmc1_deadlock                         false
% 3.35/1.00  --bmc1_ucm                              false
% 3.35/1.00  --bmc1_add_unsat_core                   none
% 3.35/1.00  --bmc1_unsat_core_children              false
% 3.35/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/1.00  --bmc1_out_stat                         full
% 3.35/1.00  --bmc1_ground_init                      false
% 3.35/1.00  --bmc1_pre_inst_next_state              false
% 3.35/1.00  --bmc1_pre_inst_state                   false
% 3.35/1.00  --bmc1_pre_inst_reach_state             false
% 3.35/1.00  --bmc1_out_unsat_core                   false
% 3.35/1.00  --bmc1_aig_witness_out                  false
% 3.35/1.00  --bmc1_verbose                          false
% 3.35/1.00  --bmc1_dump_clauses_tptp                false
% 3.35/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.35/1.00  --bmc1_dump_file                        -
% 3.35/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.35/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.35/1.00  --bmc1_ucm_extend_mode                  1
% 3.35/1.00  --bmc1_ucm_init_mode                    2
% 3.35/1.00  --bmc1_ucm_cone_mode                    none
% 3.35/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.35/1.00  --bmc1_ucm_relax_model                  4
% 3.35/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.35/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/1.00  --bmc1_ucm_layered_model                none
% 3.35/1.00  --bmc1_ucm_max_lemma_size               10
% 3.35/1.00  
% 3.35/1.00  ------ AIG Options
% 3.35/1.00  
% 3.35/1.00  --aig_mode                              false
% 3.35/1.00  
% 3.35/1.00  ------ Instantiation Options
% 3.35/1.00  
% 3.35/1.00  --instantiation_flag                    true
% 3.35/1.00  --inst_sos_flag                         false
% 3.35/1.00  --inst_sos_phase                        true
% 3.35/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/1.00  --inst_lit_sel_side                     num_symb
% 3.35/1.00  --inst_solver_per_active                1400
% 3.35/1.00  --inst_solver_calls_frac                1.
% 3.35/1.00  --inst_passive_queue_type               priority_queues
% 3.35/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/1.00  --inst_passive_queues_freq              [25;2]
% 3.35/1.00  --inst_dismatching                      true
% 3.35/1.00  --inst_eager_unprocessed_to_passive     true
% 3.35/1.00  --inst_prop_sim_given                   true
% 3.35/1.00  --inst_prop_sim_new                     false
% 3.35/1.00  --inst_subs_new                         false
% 3.35/1.00  --inst_eq_res_simp                      false
% 3.35/1.00  --inst_subs_given                       false
% 3.35/1.00  --inst_orphan_elimination               true
% 3.35/1.00  --inst_learning_loop_flag               true
% 3.35/1.00  --inst_learning_start                   3000
% 3.35/1.00  --inst_learning_factor                  2
% 3.35/1.00  --inst_start_prop_sim_after_learn       3
% 3.35/1.00  --inst_sel_renew                        solver
% 3.35/1.00  --inst_lit_activity_flag                true
% 3.35/1.00  --inst_restr_to_given                   false
% 3.35/1.00  --inst_activity_threshold               500
% 3.35/1.00  --inst_out_proof                        true
% 3.35/1.00  
% 3.35/1.00  ------ Resolution Options
% 3.35/1.00  
% 3.35/1.00  --resolution_flag                       true
% 3.35/1.00  --res_lit_sel                           adaptive
% 3.35/1.00  --res_lit_sel_side                      none
% 3.35/1.00  --res_ordering                          kbo
% 3.35/1.00  --res_to_prop_solver                    active
% 3.35/1.00  --res_prop_simpl_new                    false
% 3.35/1.00  --res_prop_simpl_given                  true
% 3.35/1.00  --res_passive_queue_type                priority_queues
% 3.35/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/1.00  --res_passive_queues_freq               [15;5]
% 3.35/1.00  --res_forward_subs                      full
% 3.35/1.00  --res_backward_subs                     full
% 3.35/1.00  --res_forward_subs_resolution           true
% 3.35/1.00  --res_backward_subs_resolution          true
% 3.35/1.00  --res_orphan_elimination                true
% 3.35/1.00  --res_time_limit                        2.
% 3.35/1.00  --res_out_proof                         true
% 3.35/1.00  
% 3.35/1.00  ------ Superposition Options
% 3.35/1.00  
% 3.35/1.00  --superposition_flag                    true
% 3.35/1.00  --sup_passive_queue_type                priority_queues
% 3.35/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.35/1.00  --demod_completeness_check              fast
% 3.35/1.00  --demod_use_ground                      true
% 3.35/1.00  --sup_to_prop_solver                    passive
% 3.35/1.00  --sup_prop_simpl_new                    true
% 3.35/1.00  --sup_prop_simpl_given                  true
% 3.35/1.00  --sup_fun_splitting                     false
% 3.35/1.00  --sup_smt_interval                      50000
% 3.35/1.00  
% 3.35/1.00  ------ Superposition Simplification Setup
% 3.35/1.00  
% 3.35/1.00  --sup_indices_passive                   []
% 3.35/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_full_bw                           [BwDemod]
% 3.35/1.00  --sup_immed_triv                        [TrivRules]
% 3.35/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_immed_bw_main                     []
% 3.35/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.00  
% 3.35/1.00  ------ Combination Options
% 3.35/1.00  
% 3.35/1.00  --comb_res_mult                         3
% 3.35/1.00  --comb_sup_mult                         2
% 3.35/1.00  --comb_inst_mult                        10
% 3.35/1.00  
% 3.35/1.00  ------ Debug Options
% 3.35/1.00  
% 3.35/1.00  --dbg_backtrace                         false
% 3.35/1.00  --dbg_dump_prop_clauses                 false
% 3.35/1.00  --dbg_dump_prop_clauses_file            -
% 3.35/1.00  --dbg_out_stat                          false
% 3.35/1.00  ------ Parsing...
% 3.35/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  ------ Proving...
% 3.35/1.00  ------ Problem Properties 
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  clauses                                 32
% 3.35/1.00  conjectures                             5
% 3.35/1.00  EPR                                     2
% 3.35/1.00  Horn                                    28
% 3.35/1.00  unary                                   8
% 3.35/1.00  binary                                  5
% 3.35/1.00  lits                                    95
% 3.35/1.00  lits eq                                 25
% 3.35/1.00  fd_pure                                 0
% 3.35/1.00  fd_pseudo                               0
% 3.35/1.00  fd_cond                                 3
% 3.35/1.00  fd_pseudo_cond                          0
% 3.35/1.00  AC symbols                              0
% 3.35/1.00  
% 3.35/1.00  ------ Schedule dynamic 5 is on 
% 3.35/1.00  
% 3.35/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ 
% 3.35/1.00  Current options:
% 3.35/1.00  ------ 
% 3.35/1.00  
% 3.35/1.00  ------ Input Options
% 3.35/1.00  
% 3.35/1.00  --out_options                           all
% 3.35/1.00  --tptp_safe_out                         true
% 3.35/1.00  --problem_path                          ""
% 3.35/1.00  --include_path                          ""
% 3.35/1.00  --clausifier                            res/vclausify_rel
% 3.35/1.00  --clausifier_options                    --mode clausify
% 3.35/1.00  --stdin                                 false
% 3.35/1.00  --stats_out                             all
% 3.35/1.00  
% 3.35/1.00  ------ General Options
% 3.35/1.00  
% 3.35/1.00  --fof                                   false
% 3.35/1.00  --time_out_real                         305.
% 3.35/1.00  --time_out_virtual                      -1.
% 3.35/1.00  --symbol_type_check                     false
% 3.35/1.00  --clausify_out                          false
% 3.35/1.00  --sig_cnt_out                           false
% 3.35/1.00  --trig_cnt_out                          false
% 3.35/1.00  --trig_cnt_out_tolerance                1.
% 3.35/1.00  --trig_cnt_out_sk_spl                   false
% 3.35/1.00  --abstr_cl_out                          false
% 3.35/1.00  
% 3.35/1.00  ------ Global Options
% 3.35/1.00  
% 3.35/1.00  --schedule                              default
% 3.35/1.00  --add_important_lit                     false
% 3.35/1.00  --prop_solver_per_cl                    1000
% 3.35/1.00  --min_unsat_core                        false
% 3.35/1.00  --soft_assumptions                      false
% 3.35/1.00  --soft_lemma_size                       3
% 3.35/1.00  --prop_impl_unit_size                   0
% 3.35/1.00  --prop_impl_unit                        []
% 3.35/1.00  --share_sel_clauses                     true
% 3.35/1.00  --reset_solvers                         false
% 3.35/1.00  --bc_imp_inh                            [conj_cone]
% 3.35/1.00  --conj_cone_tolerance                   3.
% 3.35/1.00  --extra_neg_conj                        none
% 3.35/1.00  --large_theory_mode                     true
% 3.35/1.00  --prolific_symb_bound                   200
% 3.35/1.00  --lt_threshold                          2000
% 3.35/1.00  --clause_weak_htbl                      true
% 3.35/1.00  --gc_record_bc_elim                     false
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing Options
% 3.35/1.00  
% 3.35/1.00  --preprocessing_flag                    true
% 3.35/1.00  --time_out_prep_mult                    0.1
% 3.35/1.00  --splitting_mode                        input
% 3.35/1.00  --splitting_grd                         true
% 3.35/1.00  --splitting_cvd                         false
% 3.35/1.00  --splitting_cvd_svl                     false
% 3.35/1.00  --splitting_nvd                         32
% 3.35/1.00  --sub_typing                            true
% 3.35/1.00  --prep_gs_sim                           true
% 3.35/1.00  --prep_unflatten                        true
% 3.35/1.00  --prep_res_sim                          true
% 3.35/1.00  --prep_upred                            true
% 3.35/1.00  --prep_sem_filter                       exhaustive
% 3.35/1.00  --prep_sem_filter_out                   false
% 3.35/1.00  --pred_elim                             true
% 3.35/1.00  --res_sim_input                         true
% 3.35/1.00  --eq_ax_congr_red                       true
% 3.35/1.00  --pure_diseq_elim                       true
% 3.35/1.00  --brand_transform                       false
% 3.35/1.00  --non_eq_to_eq                          false
% 3.35/1.00  --prep_def_merge                        true
% 3.35/1.00  --prep_def_merge_prop_impl              false
% 3.35/1.00  --prep_def_merge_mbd                    true
% 3.35/1.00  --prep_def_merge_tr_red                 false
% 3.35/1.00  --prep_def_merge_tr_cl                  false
% 3.35/1.00  --smt_preprocessing                     true
% 3.35/1.00  --smt_ac_axioms                         fast
% 3.35/1.00  --preprocessed_out                      false
% 3.35/1.00  --preprocessed_stats                    false
% 3.35/1.00  
% 3.35/1.00  ------ Abstraction refinement Options
% 3.35/1.00  
% 3.35/1.00  --abstr_ref                             []
% 3.35/1.00  --abstr_ref_prep                        false
% 3.35/1.00  --abstr_ref_until_sat                   false
% 3.35/1.00  --abstr_ref_sig_restrict                funpre
% 3.35/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/1.00  --abstr_ref_under                       []
% 3.35/1.00  
% 3.35/1.00  ------ SAT Options
% 3.35/1.00  
% 3.35/1.00  --sat_mode                              false
% 3.35/1.00  --sat_fm_restart_options                ""
% 3.35/1.00  --sat_gr_def                            false
% 3.35/1.00  --sat_epr_types                         true
% 3.35/1.00  --sat_non_cyclic_types                  false
% 3.35/1.00  --sat_finite_models                     false
% 3.35/1.00  --sat_fm_lemmas                         false
% 3.35/1.00  --sat_fm_prep                           false
% 3.35/1.00  --sat_fm_uc_incr                        true
% 3.35/1.00  --sat_out_model                         small
% 3.35/1.00  --sat_out_clauses                       false
% 3.35/1.00  
% 3.35/1.00  ------ QBF Options
% 3.35/1.00  
% 3.35/1.00  --qbf_mode                              false
% 3.35/1.00  --qbf_elim_univ                         false
% 3.35/1.00  --qbf_dom_inst                          none
% 3.35/1.00  --qbf_dom_pre_inst                      false
% 3.35/1.00  --qbf_sk_in                             false
% 3.35/1.00  --qbf_pred_elim                         true
% 3.35/1.00  --qbf_split                             512
% 3.35/1.00  
% 3.35/1.00  ------ BMC1 Options
% 3.35/1.00  
% 3.35/1.00  --bmc1_incremental                      false
% 3.35/1.00  --bmc1_axioms                           reachable_all
% 3.35/1.00  --bmc1_min_bound                        0
% 3.35/1.00  --bmc1_max_bound                        -1
% 3.35/1.00  --bmc1_max_bound_default                -1
% 3.35/1.00  --bmc1_symbol_reachability              true
% 3.35/1.00  --bmc1_property_lemmas                  false
% 3.35/1.00  --bmc1_k_induction                      false
% 3.35/1.00  --bmc1_non_equiv_states                 false
% 3.35/1.00  --bmc1_deadlock                         false
% 3.35/1.00  --bmc1_ucm                              false
% 3.35/1.00  --bmc1_add_unsat_core                   none
% 3.35/1.00  --bmc1_unsat_core_children              false
% 3.35/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/1.00  --bmc1_out_stat                         full
% 3.35/1.00  --bmc1_ground_init                      false
% 3.35/1.00  --bmc1_pre_inst_next_state              false
% 3.35/1.00  --bmc1_pre_inst_state                   false
% 3.35/1.00  --bmc1_pre_inst_reach_state             false
% 3.35/1.00  --bmc1_out_unsat_core                   false
% 3.35/1.00  --bmc1_aig_witness_out                  false
% 3.35/1.00  --bmc1_verbose                          false
% 3.35/1.00  --bmc1_dump_clauses_tptp                false
% 3.35/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.35/1.00  --bmc1_dump_file                        -
% 3.35/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.35/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.35/1.00  --bmc1_ucm_extend_mode                  1
% 3.35/1.00  --bmc1_ucm_init_mode                    2
% 3.35/1.00  --bmc1_ucm_cone_mode                    none
% 3.35/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.35/1.00  --bmc1_ucm_relax_model                  4
% 3.35/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.35/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/1.00  --bmc1_ucm_layered_model                none
% 3.35/1.00  --bmc1_ucm_max_lemma_size               10
% 3.35/1.00  
% 3.35/1.00  ------ AIG Options
% 3.35/1.00  
% 3.35/1.00  --aig_mode                              false
% 3.35/1.00  
% 3.35/1.00  ------ Instantiation Options
% 3.35/1.00  
% 3.35/1.00  --instantiation_flag                    true
% 3.35/1.00  --inst_sos_flag                         false
% 3.35/1.00  --inst_sos_phase                        true
% 3.35/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/1.00  --inst_lit_sel_side                     none
% 3.35/1.00  --inst_solver_per_active                1400
% 3.35/1.00  --inst_solver_calls_frac                1.
% 3.35/1.00  --inst_passive_queue_type               priority_queues
% 3.35/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/1.00  --inst_passive_queues_freq              [25;2]
% 3.35/1.00  --inst_dismatching                      true
% 3.35/1.00  --inst_eager_unprocessed_to_passive     true
% 3.35/1.00  --inst_prop_sim_given                   true
% 3.35/1.00  --inst_prop_sim_new                     false
% 3.35/1.00  --inst_subs_new                         false
% 3.35/1.00  --inst_eq_res_simp                      false
% 3.35/1.00  --inst_subs_given                       false
% 3.35/1.00  --inst_orphan_elimination               true
% 3.35/1.00  --inst_learning_loop_flag               true
% 3.35/1.00  --inst_learning_start                   3000
% 3.35/1.00  --inst_learning_factor                  2
% 3.35/1.00  --inst_start_prop_sim_after_learn       3
% 3.35/1.00  --inst_sel_renew                        solver
% 3.35/1.00  --inst_lit_activity_flag                true
% 3.35/1.00  --inst_restr_to_given                   false
% 3.35/1.00  --inst_activity_threshold               500
% 3.35/1.00  --inst_out_proof                        true
% 3.35/1.00  
% 3.35/1.00  ------ Resolution Options
% 3.35/1.00  
% 3.35/1.00  --resolution_flag                       false
% 3.35/1.00  --res_lit_sel                           adaptive
% 3.35/1.00  --res_lit_sel_side                      none
% 3.35/1.00  --res_ordering                          kbo
% 3.35/1.00  --res_to_prop_solver                    active
% 3.35/1.00  --res_prop_simpl_new                    false
% 3.35/1.00  --res_prop_simpl_given                  true
% 3.35/1.00  --res_passive_queue_type                priority_queues
% 3.35/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/1.00  --res_passive_queues_freq               [15;5]
% 3.35/1.00  --res_forward_subs                      full
% 3.35/1.00  --res_backward_subs                     full
% 3.35/1.00  --res_forward_subs_resolution           true
% 3.35/1.00  --res_backward_subs_resolution          true
% 3.35/1.00  --res_orphan_elimination                true
% 3.35/1.00  --res_time_limit                        2.
% 3.35/1.00  --res_out_proof                         true
% 3.35/1.00  
% 3.35/1.00  ------ Superposition Options
% 3.35/1.00  
% 3.35/1.00  --superposition_flag                    true
% 3.35/1.00  --sup_passive_queue_type                priority_queues
% 3.35/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.35/1.00  --demod_completeness_check              fast
% 3.35/1.00  --demod_use_ground                      true
% 3.35/1.00  --sup_to_prop_solver                    passive
% 3.35/1.00  --sup_prop_simpl_new                    true
% 3.35/1.00  --sup_prop_simpl_given                  true
% 3.35/1.00  --sup_fun_splitting                     false
% 3.35/1.00  --sup_smt_interval                      50000
% 3.35/1.00  
% 3.35/1.00  ------ Superposition Simplification Setup
% 3.35/1.00  
% 3.35/1.00  --sup_indices_passive                   []
% 3.35/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_full_bw                           [BwDemod]
% 3.35/1.00  --sup_immed_triv                        [TrivRules]
% 3.35/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_immed_bw_main                     []
% 3.35/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.00  
% 3.35/1.00  ------ Combination Options
% 3.35/1.00  
% 3.35/1.00  --comb_res_mult                         3
% 3.35/1.00  --comb_sup_mult                         2
% 3.35/1.00  --comb_inst_mult                        10
% 3.35/1.00  
% 3.35/1.00  ------ Debug Options
% 3.35/1.00  
% 3.35/1.00  --dbg_backtrace                         false
% 3.35/1.00  --dbg_dump_prop_clauses                 false
% 3.35/1.00  --dbg_dump_prop_clauses_file            -
% 3.35/1.00  --dbg_out_stat                          false
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  % SZS status Theorem for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  fof(f16,conjecture,(
% 3.35/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f17,negated_conjecture,(
% 3.35/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.35/1.00    inference(negated_conjecture,[],[f16])).
% 3.35/1.00  
% 3.35/1.00  fof(f41,plain,(
% 3.35/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.35/1.00    inference(ennf_transformation,[],[f17])).
% 3.35/1.00  
% 3.35/1.00  fof(f42,plain,(
% 3.35/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.35/1.00    inference(flattening,[],[f41])).
% 3.35/1.00  
% 3.35/1.00  fof(f47,plain,(
% 3.35/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f46,plain,(
% 3.35/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f45,plain,(
% 3.35/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f48,plain,(
% 3.35/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.35/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).
% 3.35/1.00  
% 3.35/1.00  fof(f83,plain,(
% 3.35/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f13,axiom,(
% 3.35/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f36,plain,(
% 3.35/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.35/1.00    inference(ennf_transformation,[],[f13])).
% 3.35/1.00  
% 3.35/1.00  fof(f75,plain,(
% 3.35/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f36])).
% 3.35/1.00  
% 3.35/1.00  fof(f80,plain,(
% 3.35/1.00    l1_struct_0(sK1)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f78,plain,(
% 3.35/1.00    l1_struct_0(sK0)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f6,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f25,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(ennf_transformation,[],[f6])).
% 3.35/1.00  
% 3.35/1.00  fof(f57,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.00    inference(cnf_transformation,[],[f25])).
% 3.35/1.00  
% 3.35/1.00  fof(f84,plain,(
% 3.35/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f9,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f28,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(ennf_transformation,[],[f9])).
% 3.35/1.00  
% 3.35/1.00  fof(f29,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(flattening,[],[f28])).
% 3.35/1.00  
% 3.35/1.00  fof(f43,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(nnf_transformation,[],[f29])).
% 3.35/1.00  
% 3.35/1.00  fof(f61,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.00    inference(cnf_transformation,[],[f43])).
% 3.35/1.00  
% 3.35/1.00  fof(f8,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f27,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(ennf_transformation,[],[f8])).
% 3.35/1.00  
% 3.35/1.00  fof(f60,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.00    inference(cnf_transformation,[],[f27])).
% 3.35/1.00  
% 3.35/1.00  fof(f7,axiom,(
% 3.35/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f26,plain,(
% 3.35/1.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(ennf_transformation,[],[f7])).
% 3.35/1.00  
% 3.35/1.00  fof(f58,plain,(
% 3.35/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.00    inference(cnf_transformation,[],[f26])).
% 3.35/1.00  
% 3.35/1.00  fof(f82,plain,(
% 3.35/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f1,axiom,(
% 3.35/1.00    v1_xboole_0(k1_xboole_0)),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f49,plain,(
% 3.35/1.00    v1_xboole_0(k1_xboole_0)),
% 3.35/1.00    inference(cnf_transformation,[],[f1])).
% 3.35/1.00  
% 3.35/1.00  fof(f14,axiom,(
% 3.35/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f37,plain,(
% 3.35/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.35/1.00    inference(ennf_transformation,[],[f14])).
% 3.35/1.00  
% 3.35/1.00  fof(f38,plain,(
% 3.35/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.35/1.00    inference(flattening,[],[f37])).
% 3.35/1.00  
% 3.35/1.00  fof(f76,plain,(
% 3.35/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f38])).
% 3.35/1.00  
% 3.35/1.00  fof(f79,plain,(
% 3.35/1.00    ~v2_struct_0(sK1)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f5,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f24,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.00    inference(ennf_transformation,[],[f5])).
% 3.35/1.00  
% 3.35/1.00  fof(f56,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.00    inference(cnf_transformation,[],[f24])).
% 3.35/1.00  
% 3.35/1.00  fof(f12,axiom,(
% 3.35/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f34,plain,(
% 3.35/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.00    inference(ennf_transformation,[],[f12])).
% 3.35/1.00  
% 3.35/1.00  fof(f35,plain,(
% 3.35/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.00    inference(flattening,[],[f34])).
% 3.35/1.00  
% 3.35/1.00  fof(f74,plain,(
% 3.35/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f35])).
% 3.35/1.00  
% 3.35/1.00  fof(f73,plain,(
% 3.35/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f35])).
% 3.35/1.00  
% 3.35/1.00  fof(f11,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f32,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.35/1.00    inference(ennf_transformation,[],[f11])).
% 3.35/1.00  
% 3.35/1.00  fof(f33,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.35/1.00    inference(flattening,[],[f32])).
% 3.35/1.00  
% 3.35/1.00  fof(f71,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f33])).
% 3.35/1.00  
% 3.35/1.00  fof(f81,plain,(
% 3.35/1.00    v1_funct_1(sK2)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f85,plain,(
% 3.35/1.00    v2_funct_1(sK2)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f3,axiom,(
% 3.35/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f20,plain,(
% 3.35/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.00    inference(ennf_transformation,[],[f3])).
% 3.35/1.00  
% 3.35/1.00  fof(f21,plain,(
% 3.35/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.00    inference(flattening,[],[f20])).
% 3.35/1.00  
% 3.35/1.00  fof(f53,plain,(
% 3.35/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f21])).
% 3.35/1.00  
% 3.35/1.00  fof(f54,plain,(
% 3.35/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f21])).
% 3.35/1.00  
% 3.35/1.00  fof(f69,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f33])).
% 3.35/1.00  
% 3.35/1.00  fof(f2,axiom,(
% 3.35/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f18,plain,(
% 3.35/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.00    inference(ennf_transformation,[],[f2])).
% 3.35/1.00  
% 3.35/1.00  fof(f19,plain,(
% 3.35/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.00    inference(flattening,[],[f18])).
% 3.35/1.00  
% 3.35/1.00  fof(f51,plain,(
% 3.35/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f19])).
% 3.35/1.00  
% 3.35/1.00  fof(f4,axiom,(
% 3.35/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f22,plain,(
% 3.35/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.00    inference(ennf_transformation,[],[f4])).
% 3.35/1.00  
% 3.35/1.00  fof(f23,plain,(
% 3.35/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.00    inference(flattening,[],[f22])).
% 3.35/1.00  
% 3.35/1.00  fof(f55,plain,(
% 3.35/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f23])).
% 3.35/1.00  
% 3.35/1.00  fof(f15,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f39,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.35/1.00    inference(ennf_transformation,[],[f15])).
% 3.35/1.00  
% 3.35/1.00  fof(f40,plain,(
% 3.35/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.35/1.00    inference(flattening,[],[f39])).
% 3.35/1.00  
% 3.35/1.00  fof(f77,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f40])).
% 3.35/1.00  
% 3.35/1.00  fof(f10,axiom,(
% 3.35/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.35/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f30,plain,(
% 3.35/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.35/1.00    inference(ennf_transformation,[],[f10])).
% 3.35/1.00  
% 3.35/1.00  fof(f31,plain,(
% 3.35/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.35/1.00    inference(flattening,[],[f30])).
% 3.35/1.00  
% 3.35/1.00  fof(f44,plain,(
% 3.35/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.35/1.00    inference(nnf_transformation,[],[f31])).
% 3.35/1.00  
% 3.35/1.00  fof(f68,plain,(
% 3.35/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f44])).
% 3.35/1.00  
% 3.35/1.00  fof(f92,plain,(
% 3.35/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.35/1.00    inference(equality_resolution,[],[f68])).
% 3.35/1.00  
% 3.35/1.00  fof(f86,plain,(
% 3.35/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.35/1.00    inference(cnf_transformation,[],[f48])).
% 3.35/1.00  
% 3.35/1.00  fof(f52,plain,(
% 3.35/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f19])).
% 3.35/1.00  
% 3.35/1.00  fof(f70,plain,(
% 3.35/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f33])).
% 3.35/1.00  
% 3.35/1.00  cnf(c_32,negated_conjecture,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.35/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1176,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_26,plain,
% 3.35/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_35,negated_conjecture,
% 3.35/1.00      ( l1_struct_0(sK1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_444,plain,
% 3.35/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.35/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_445,plain,
% 3.35/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.35/1.00      inference(unflattening,[status(thm)],[c_444]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_37,negated_conjecture,
% 3.35/1.00      ( l1_struct_0(sK0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_449,plain,
% 3.35/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.35/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_450,plain,
% 3.35/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.35/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1216,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_1176,c_445,c_450]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_8,plain,
% 3.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1192,plain,
% 3.35/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1650,plain,
% 3.35/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1216,c_1192]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_31,negated_conjecture,
% 3.35/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1213,plain,
% 3.35/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_31,c_445,c_450]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1824,plain,
% 3.35/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1650,c_1213]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1877,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1824,c_1216]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_17,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.35/1.00      | k1_xboole_0 = X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1183,plain,
% 3.35/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.35/1.00      | k1_xboole_0 = X1
% 3.35/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4723,plain,
% 3.35/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1877,c_1183]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_10,plain,
% 3.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1190,plain,
% 3.35/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2468,plain,
% 3.35/1.00      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1877,c_1190]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9,plain,
% 3.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.35/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1191,plain,
% 3.35/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2470,plain,
% 3.35/1.00      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1877,c_1191]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2477,plain,
% 3.35/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_2468,c_2470]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4734,plain,
% 3.35/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_4723,c_2477]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_33,negated_conjecture,
% 3.35/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1175,plain,
% 3.35/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1210,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_1175,c_445,c_450]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1878,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1824,c_1210]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_0,plain,
% 3.35/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_27,plain,
% 3.35/1.00      ( v2_struct_0(X0)
% 3.35/1.00      | ~ l1_struct_0(X0)
% 3.35/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_417,plain,
% 3.35/1.00      ( v2_struct_0(X0)
% 3.35/1.00      | ~ l1_struct_0(X0)
% 3.35/1.00      | k2_struct_0(X0) != k1_xboole_0 ),
% 3.35/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_36,negated_conjecture,
% 3.35/1.00      ( ~ v2_struct_0(sK1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_435,plain,
% 3.35/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 3.35/1.00      inference(resolution_lifted,[status(thm)],[c_417,c_36]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_436,plain,
% 3.35/1.00      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 3.35/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_438,plain,
% 3.35/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_436,c_35]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1880,plain,
% 3.35/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1824,c_438]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5886,plain,
% 3.35/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4734,c_1878,c_1880]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7,plain,
% 3.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | v1_relat_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1193,plain,
% 3.35/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1535,plain,
% 3.35/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1216,c_1193]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_23,plain,
% 3.35/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.35/1.00      | ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1180,plain,
% 3.35/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4722,plain,
% 3.35/1.00      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.35/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.35/1.00      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1180,c_1183]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_24,plain,
% 3.35/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.35/1.00      | ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_56,plain,
% 3.35/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5662,plain,
% 3.35/1.00      ( k2_relat_1(X0) = k1_xboole_0
% 3.35/1.00      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4722,c_56]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5663,plain,
% 3.35/1.00      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.35/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(renaming,[status(thm)],[c_5662]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5673,plain,
% 3.35/1.00      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1535,c_5663]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1875,plain,
% 3.35/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1824,c_1650]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_20,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1182,plain,
% 3.35/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.35/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.35/1.00      | v1_funct_1(X2) != iProver_top
% 3.35/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3741,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1875,c_1182]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_34,negated_conjecture,
% 3.35/1.00      ( v1_funct_1(sK2) ),
% 3.35/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_41,plain,
% 3.35/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_30,negated_conjecture,
% 3.35/1.00      ( v2_funct_1(sK2) ),
% 3.35/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_44,plain,
% 3.35/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4323,plain,
% 3.35/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_3741,c_41,c_44,c_1877,c_1878]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4328,plain,
% 3.35/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_4323,c_1193]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2331,plain,
% 3.35/1.00      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1180,c_1192]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4358,plain,
% 3.35/1.00      ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_4328,c_2331]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5,plain,
% 3.35/1.00      ( ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1195,plain,
% 3.35/1.00      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3988,plain,
% 3.35/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1535,c_1195]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1459,plain,
% 3.35/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.35/1.00      | v1_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1538,plain,
% 3.35/1.00      ( ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4172,plain,
% 3.35/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_3988,c_34,c_32,c_30,c_1459,c_1538]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4,plain,
% 3.35/1.00      ( ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1196,plain,
% 3.35/1.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4136,plain,
% 3.35/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1535,c_1196]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1541,plain,
% 3.35/1.00      ( ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4192,plain,
% 3.35/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4136,c_34,c_32,c_30,c_1459,c_1541]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4366,plain,
% 3.35/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_4358,c_4172,c_4192]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_22,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2,plain,
% 3.35/1.00      ( ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.35/1.00      | ~ v2_funct_1(X0) ),
% 3.35/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_217,plain,
% 3.35/1.00      ( ~ v2_funct_1(X0)
% 3.35/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_22,c_7,c_2]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_218,plain,
% 3.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.35/1.00      | ~ v2_funct_1(X0) ),
% 3.35/1.00      inference(renaming,[status(thm)],[c_217]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1173,plain,
% 3.35/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.35/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1530,plain,
% 3.35/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1216,c_1173]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4675,plain,
% 3.35/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4366,c_41,c_44,c_1530]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4678,plain,
% 3.35/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_4675,c_1182]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6,plain,
% 3.35/1.00      ( ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1194,plain,
% 3.35/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2814,plain,
% 3.35/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1535,c_1194]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1537,plain,
% 3.35/1.00      ( ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3076,plain,
% 3.35/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_2814,c_34,c_32,c_30,c_1459,c_1537]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4708,plain,
% 3.35/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_4678,c_3076]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_43,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1460,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.35/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1539,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.35/1.00      | ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1560,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.35/1.00      | v1_relat_1(sK2) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1539]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5206,plain,
% 3.35/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4708,c_41,c_43,c_1460,c_1560]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5214,plain,
% 3.35/1.00      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_5206,c_1190]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2330,plain,
% 3.35/1.00      ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1180,c_1191]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3496,plain,
% 3.35/1.00      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1535,c_2330]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1730,plain,
% 3.35/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.35/1.00      | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4160,plain,
% 3.35/1.00      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_3496,c_34,c_32,c_1459,c_1539,c_1730]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5222,plain,
% 3.35/1.00      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_5214,c_4160]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5686,plain,
% 3.35/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_5673,c_5222]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1540,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.35/1.00      | ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1558,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.35/1.00      | v1_relat_1(sK2) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5213,plain,
% 3.35/1.00      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_5206,c_1183]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5224,plain,
% 3.35/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 3.35/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.35/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_5213,c_5222]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5876,plain,
% 3.35/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_5686,c_41,c_43,c_1460,c_1558,c_1880,c_5224]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5888,plain,
% 3.35/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_5886,c_5876]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_28,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.35/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1178,plain,
% 3.35/1.00      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.35/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.35/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.35/1.00      | v1_funct_1(X2) != iProver_top
% 3.35/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2067,plain,
% 3.35/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.35/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1875,c_1178]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2600,plain,
% 3.35/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_2067,c_41,c_44,c_1877,c_1878]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_18,plain,
% 3.35/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.35/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.35/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/1.00      | ~ v1_funct_1(X2) ),
% 3.35/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_29,negated_conjecture,
% 3.35/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.35/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_458,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.35/1.00      | u1_struct_0(sK1) != X2
% 3.35/1.00      | u1_struct_0(sK0) != X1
% 3.35/1.00      | sK2 != X0 ),
% 3.35/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_459,plain,
% 3.35/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.35/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.35/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.35/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.35/1.00      inference(unflattening,[status(thm)],[c_458]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1172,plain,
% 3.35/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.35/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1385,plain,
% 3.35/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.35/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_1172,c_445,c_450]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1876,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.35/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_1824,c_1385]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2603,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.35/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_2600,c_1876]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5896,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.35/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_5888,c_2603]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4680,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.35/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_4675,c_1178]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4686,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.35/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_4680,c_3076]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1,plain,
% 3.35/1.00      ( ~ v1_relat_1(X0)
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | v2_funct_1(k2_funct_1(X0)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1545,plain,
% 3.35/1.00      ( ~ v1_relat_1(sK2)
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2))
% 3.35/1.00      | ~ v2_funct_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1546,plain,
% 3.35/1.00      ( v1_relat_1(sK2) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1731,plain,
% 3.35/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.35/1.00      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1510,plain,
% 3.35/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.35/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1756,plain,
% 3.35/1.00      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.35/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1757,plain,
% 3.35/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.35/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1756]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_21,plain,
% 3.35/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.35/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.00      | ~ v1_funct_1(X0)
% 3.35/1.00      | ~ v2_funct_1(X0)
% 3.35/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1515,plain,
% 3.35/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.35/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 3.35/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1761,plain,
% 3.35/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.35/1.00      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.35/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.35/1.00      | ~ v1_funct_1(sK2)
% 3.35/1.00      | ~ v2_funct_1(sK2)
% 3.35/1.00      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_1515]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1762,plain,
% 3.35/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.35/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.35/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top
% 3.35/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5202,plain,
% 3.35/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_4686,c_34,c_41,c_32,c_43,c_44,c_1459,c_1460,c_1530,
% 3.35/1.00                 c_1546,c_1558,c_1539,c_1560,c_1731,c_1757,c_1762]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5910,plain,
% 3.35/1.00      ( sK2 != sK2
% 3.35/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(light_normalisation,[status(thm)],[c_5896,c_5202]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5911,plain,
% 3.35/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.35/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.35/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.35/1.00      inference(equality_resolution_simp,[status(thm)],[c_5910]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(contradiction,plain,
% 3.35/1.00      ( $false ),
% 3.35/1.00      inference(minisat,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_5911,c_1560,c_1558,c_1460,c_43,c_41]) ).
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  ------                               Statistics
% 3.35/1.00  
% 3.35/1.00  ------ General
% 3.35/1.00  
% 3.35/1.00  abstr_ref_over_cycles:                  0
% 3.35/1.00  abstr_ref_under_cycles:                 0
% 3.35/1.00  gc_basic_clause_elim:                   0
% 3.35/1.00  forced_gc_time:                         0
% 3.35/1.00  parsing_time:                           0.011
% 3.35/1.00  unif_index_cands_time:                  0.
% 3.35/1.00  unif_index_add_time:                    0.
% 3.35/1.00  orderings_time:                         0.
% 3.35/1.00  out_proof_time:                         0.034
% 3.35/1.00  total_time:                             0.288
% 3.35/1.00  num_of_symbols:                         57
% 3.35/1.00  num_of_terms:                           5093
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing
% 3.35/1.00  
% 3.35/1.00  num_of_splits:                          0
% 3.35/1.00  num_of_split_atoms:                     0
% 3.35/1.00  num_of_reused_defs:                     0
% 3.35/1.00  num_eq_ax_congr_red:                    36
% 3.35/1.00  num_of_sem_filtered_clauses:            1
% 3.35/1.00  num_of_subtypes:                        0
% 3.35/1.00  monotx_restored_types:                  0
% 3.35/1.00  sat_num_of_epr_types:                   0
% 3.35/1.00  sat_num_of_non_cyclic_types:            0
% 3.35/1.00  sat_guarded_non_collapsed_types:        0
% 3.35/1.00  num_pure_diseq_elim:                    0
% 3.35/1.00  simp_replaced_by:                       0
% 3.35/1.00  res_preprocessed:                       168
% 3.35/1.00  prep_upred:                             0
% 3.35/1.00  prep_unflattend:                        10
% 3.35/1.00  smt_new_axioms:                         0
% 3.35/1.00  pred_elim_cands:                        5
% 3.35/1.00  pred_elim:                              4
% 3.35/1.00  pred_elim_cl:                           5
% 3.35/1.00  pred_elim_cycles:                       6
% 3.35/1.00  merged_defs:                            0
% 3.35/1.00  merged_defs_ncl:                        0
% 3.35/1.00  bin_hyper_res:                          0
% 3.35/1.00  prep_cycles:                            4
% 3.35/1.00  pred_elim_time:                         0.003
% 3.35/1.00  splitting_time:                         0.
% 3.35/1.00  sem_filter_time:                        0.
% 3.35/1.00  monotx_time:                            0.
% 3.35/1.00  subtype_inf_time:                       0.
% 3.35/1.00  
% 3.35/1.00  ------ Problem properties
% 3.35/1.00  
% 3.35/1.00  clauses:                                32
% 3.35/1.00  conjectures:                            5
% 3.35/1.00  epr:                                    2
% 3.35/1.00  horn:                                   28
% 3.35/1.00  ground:                                 9
% 3.35/1.00  unary:                                  8
% 3.35/1.00  binary:                                 5
% 3.35/1.00  lits:                                   95
% 3.35/1.00  lits_eq:                                25
% 3.35/1.00  fd_pure:                                0
% 3.35/1.00  fd_pseudo:                              0
% 3.35/1.00  fd_cond:                                3
% 3.35/1.00  fd_pseudo_cond:                         0
% 3.35/1.00  ac_symbols:                             0
% 3.35/1.00  
% 3.35/1.00  ------ Propositional Solver
% 3.35/1.00  
% 3.35/1.00  prop_solver_calls:                      28
% 3.35/1.00  prop_fast_solver_calls:                 1253
% 3.35/1.00  smt_solver_calls:                       0
% 3.35/1.00  smt_fast_solver_calls:                  0
% 3.35/1.00  prop_num_of_clauses:                    2035
% 3.35/1.00  prop_preprocess_simplified:             6500
% 3.35/1.00  prop_fo_subsumed:                       65
% 3.35/1.00  prop_solver_time:                       0.
% 3.35/1.00  smt_solver_time:                        0.
% 3.35/1.00  smt_fast_solver_time:                   0.
% 3.35/1.00  prop_fast_solver_time:                  0.
% 3.35/1.00  prop_unsat_core_time:                   0.
% 3.35/1.00  
% 3.35/1.00  ------ QBF
% 3.35/1.00  
% 3.35/1.00  qbf_q_res:                              0
% 3.35/1.00  qbf_num_tautologies:                    0
% 3.35/1.00  qbf_prep_cycles:                        0
% 3.35/1.00  
% 3.35/1.00  ------ BMC1
% 3.35/1.00  
% 3.35/1.00  bmc1_current_bound:                     -1
% 3.35/1.00  bmc1_last_solved_bound:                 -1
% 3.35/1.00  bmc1_unsat_core_size:                   -1
% 3.35/1.00  bmc1_unsat_core_parents_size:           -1
% 3.35/1.00  bmc1_merge_next_fun:                    0
% 3.35/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.35/1.00  
% 3.35/1.00  ------ Instantiation
% 3.35/1.00  
% 3.35/1.00  inst_num_of_clauses:                    733
% 3.35/1.00  inst_num_in_passive:                    66
% 3.35/1.00  inst_num_in_active:                     366
% 3.35/1.00  inst_num_in_unprocessed:                301
% 3.35/1.00  inst_num_of_loops:                      380
% 3.35/1.00  inst_num_of_learning_restarts:          0
% 3.35/1.00  inst_num_moves_active_passive:          10
% 3.35/1.00  inst_lit_activity:                      0
% 3.35/1.00  inst_lit_activity_moves:                0
% 3.35/1.00  inst_num_tautologies:                   0
% 3.35/1.00  inst_num_prop_implied:                  0
% 3.35/1.00  inst_num_existing_simplified:           0
% 3.35/1.00  inst_num_eq_res_simplified:             0
% 3.35/1.00  inst_num_child_elim:                    0
% 3.35/1.00  inst_num_of_dismatching_blockings:      55
% 3.35/1.00  inst_num_of_non_proper_insts:           461
% 3.35/1.00  inst_num_of_duplicates:                 0
% 3.35/1.00  inst_inst_num_from_inst_to_res:         0
% 3.35/1.00  inst_dismatching_checking_time:         0.
% 3.35/1.00  
% 3.35/1.00  ------ Resolution
% 3.35/1.00  
% 3.35/1.00  res_num_of_clauses:                     0
% 3.35/1.00  res_num_in_passive:                     0
% 3.35/1.00  res_num_in_active:                      0
% 3.35/1.00  res_num_of_loops:                       172
% 3.35/1.00  res_forward_subset_subsumed:            34
% 3.35/1.00  res_backward_subset_subsumed:           0
% 3.35/1.00  res_forward_subsumed:                   0
% 3.35/1.00  res_backward_subsumed:                  0
% 3.35/1.00  res_forward_subsumption_resolution:     0
% 3.35/1.00  res_backward_subsumption_resolution:    0
% 3.35/1.00  res_clause_to_clause_subsumption:       148
% 3.35/1.00  res_orphan_elimination:                 0
% 3.35/1.00  res_tautology_del:                      46
% 3.35/1.00  res_num_eq_res_simplified:              0
% 3.35/1.00  res_num_sel_changes:                    0
% 3.35/1.00  res_moves_from_active_to_pass:          0
% 3.35/1.00  
% 3.35/1.00  ------ Superposition
% 3.35/1.00  
% 3.35/1.00  sup_time_total:                         0.
% 3.35/1.00  sup_time_generating:                    0.
% 3.35/1.00  sup_time_sim_full:                      0.
% 3.35/1.00  sup_time_sim_immed:                     0.
% 3.35/1.00  
% 3.35/1.00  sup_num_of_clauses:                     71
% 3.35/1.00  sup_num_in_active:                      51
% 3.35/1.00  sup_num_in_passive:                     20
% 3.35/1.00  sup_num_of_loops:                       75
% 3.35/1.00  sup_fw_superposition:                   30
% 3.35/1.00  sup_bw_superposition:                   55
% 3.35/1.00  sup_immediate_simplified:               42
% 3.35/1.00  sup_given_eliminated:                   0
% 3.35/1.00  comparisons_done:                       0
% 3.35/1.00  comparisons_avoided:                    6
% 3.35/1.00  
% 3.35/1.00  ------ Simplifications
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  sim_fw_subset_subsumed:                 8
% 3.35/1.00  sim_bw_subset_subsumed:                 4
% 3.35/1.00  sim_fw_subsumed:                        4
% 3.35/1.00  sim_bw_subsumed:                        0
% 3.35/1.00  sim_fw_subsumption_res:                 0
% 3.35/1.00  sim_bw_subsumption_res:                 0
% 3.35/1.00  sim_tautology_del:                      1
% 3.35/1.00  sim_eq_tautology_del:                   6
% 3.35/1.00  sim_eq_res_simp:                        2
% 3.35/1.00  sim_fw_demodulated:                     10
% 3.35/1.00  sim_bw_demodulated:                     24
% 3.35/1.00  sim_light_normalised:                   34
% 3.35/1.00  sim_joinable_taut:                      0
% 3.35/1.00  sim_joinable_simp:                      0
% 3.35/1.00  sim_ac_normalised:                      0
% 3.35/1.00  sim_smt_subsumption:                    0
% 3.35/1.00  
%------------------------------------------------------------------------------
