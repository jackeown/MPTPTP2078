%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:36 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  213 (6744 expanded)
%              Number of clauses        :  135 (1904 expanded)
%              Number of leaves         :   22 (1991 expanded)
%              Depth                    :   26
%              Number of atoms          :  793 (43987 expanded)
%              Number of equality atoms :  298 (7271 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3)
        & v2_funct_1(sK3)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
              ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)
    & v2_funct_1(sK3)
    & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53,f52,f51])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1192,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_422,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_423,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_427,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_428,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1240,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1192,c_423,c_428])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1990,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1213])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1793,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1853,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1854,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_3113,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_43,c_1793,c_1854])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_409,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_410,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_50,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_412,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_36,c_35,c_50])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_412])).

cnf(c_435,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_435,c_16])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_508,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_492,c_11])).

cnf(c_1187,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1304,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1187,c_423])).

cnf(c_1743,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1304])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1191,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1232,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1191,c_423,c_428])).

cnf(c_1811,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_41,c_1232])).

cnf(c_3118,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3113,c_1811])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1202,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1979,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1240,c_1202])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1237,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_31,c_423,c_428])).

cnf(c_2393,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1979,c_1237])).

cnf(c_22,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_702,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sP0_iProver_split
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_458])).

cnf(c_1188,plain,
    ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1391,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1188,c_423,c_428])).

cnf(c_701,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_458])).

cnf(c_1189,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1295,plain,
    ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1189,c_423,c_428])).

cnf(c_1397,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1391,c_1295])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1194,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1674,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1194])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1782,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1674,c_41,c_44,c_1232,c_1240])).

cnf(c_1818,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1397,c_1782])).

cnf(c_2430,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2393,c_1818])).

cnf(c_3865,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3118,c_2430])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_53,plain,
    ( ~ l1_struct_0(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1547,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1571,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1632,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1697,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1698,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1642,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1700,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1701,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1700])).

cnf(c_705,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1733,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1856,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_711,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1491,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2034,plain,
    ( v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v2_funct_1(k6_relat_1(k1_relat_1(sK3)))
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_2035,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3))
    | v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) = iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1597,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(sK3,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2101,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_2167,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2101])).

cnf(c_2169,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_2173,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2169])).

cnf(c_2,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2425,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2426,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_2472,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2473,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2472])).

cnf(c_2434,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2393,c_1240])).

cnf(c_3866,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3118,c_2434])).

cnf(c_2435,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2393,c_1232])).

cnf(c_3869,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3118,c_2435])).

cnf(c_2429,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2393,c_1979])).

cnf(c_3868,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3118,c_2429])).

cnf(c_1197,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3997,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_1197])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1196,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3998,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_1196])).

cnf(c_3126,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1197])).

cnf(c_4224,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_41,c_44,c_2434,c_2435])).

cnf(c_4228,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4224,c_3118])).

cnf(c_4232,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4228,c_1202])).

cnf(c_1190,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1207,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2616,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1207])).

cnf(c_1536,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2818,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2616,c_34,c_32,c_30,c_1536,c_1792,c_1853])).

cnf(c_4234,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4232,c_2818])).

cnf(c_4339,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_1194])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1203,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2056,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1203])).

cnf(c_1555,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2200,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2056,c_34,c_32,c_30,c_1555,c_1792,c_1853])).

cnf(c_4345,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = sK3
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4339,c_2200])).

cnf(c_4568,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3865,c_35,c_34,c_41,c_42,c_32,c_43,c_31,c_30,c_44,c_53,c_1547,c_1571,c_1698,c_1701,c_1792,c_1793,c_1853,c_1854,c_1856,c_2035,c_2167,c_2173,c_2426,c_2473,c_3866,c_3869,c_3997,c_3998,c_4345])).

cnf(c_4452,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_35,c_34,c_41,c_42,c_32,c_43,c_31,c_30,c_44,c_53,c_1547,c_1571,c_1698,c_1701,c_1792,c_1793,c_1853,c_1854,c_1856,c_2035,c_2167,c_2173,c_2426,c_2473,c_3866,c_3869,c_3997,c_3998])).

cnf(c_4572,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4568,c_4452])).

cnf(c_4576,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4572,c_1190,c_3866,c_3869])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.85/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.00  
% 2.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/1.00  
% 2.85/1.00  ------  iProver source info
% 2.85/1.00  
% 2.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/1.00  git: non_committed_changes: false
% 2.85/1.00  git: last_make_outside_of_git: false
% 2.85/1.00  
% 2.85/1.00  ------ 
% 2.85/1.00  
% 2.85/1.00  ------ Input Options
% 2.85/1.00  
% 2.85/1.00  --out_options                           all
% 2.85/1.00  --tptp_safe_out                         true
% 2.85/1.00  --problem_path                          ""
% 2.85/1.00  --include_path                          ""
% 2.85/1.00  --clausifier                            res/vclausify_rel
% 2.85/1.00  --clausifier_options                    --mode clausify
% 2.85/1.00  --stdin                                 false
% 2.85/1.00  --stats_out                             all
% 2.85/1.00  
% 2.85/1.00  ------ General Options
% 2.85/1.00  
% 2.85/1.00  --fof                                   false
% 2.85/1.00  --time_out_real                         305.
% 2.85/1.00  --time_out_virtual                      -1.
% 2.85/1.00  --symbol_type_check                     false
% 2.85/1.00  --clausify_out                          false
% 2.85/1.00  --sig_cnt_out                           false
% 2.85/1.00  --trig_cnt_out                          false
% 2.85/1.00  --trig_cnt_out_tolerance                1.
% 2.85/1.00  --trig_cnt_out_sk_spl                   false
% 2.85/1.00  --abstr_cl_out                          false
% 2.85/1.00  
% 2.85/1.00  ------ Global Options
% 2.85/1.00  
% 2.85/1.00  --schedule                              default
% 2.85/1.00  --add_important_lit                     false
% 2.85/1.00  --prop_solver_per_cl                    1000
% 2.85/1.00  --min_unsat_core                        false
% 2.85/1.00  --soft_assumptions                      false
% 2.85/1.00  --soft_lemma_size                       3
% 2.85/1.00  --prop_impl_unit_size                   0
% 2.85/1.00  --prop_impl_unit                        []
% 2.85/1.00  --share_sel_clauses                     true
% 2.85/1.00  --reset_solvers                         false
% 2.85/1.00  --bc_imp_inh                            [conj_cone]
% 2.85/1.00  --conj_cone_tolerance                   3.
% 2.85/1.00  --extra_neg_conj                        none
% 2.85/1.00  --large_theory_mode                     true
% 2.85/1.00  --prolific_symb_bound                   200
% 2.85/1.00  --lt_threshold                          2000
% 2.85/1.00  --clause_weak_htbl                      true
% 2.85/1.00  --gc_record_bc_elim                     false
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing Options
% 2.85/1.00  
% 2.85/1.00  --preprocessing_flag                    true
% 2.85/1.00  --time_out_prep_mult                    0.1
% 2.85/1.00  --splitting_mode                        input
% 2.85/1.00  --splitting_grd                         true
% 2.85/1.00  --splitting_cvd                         false
% 2.85/1.00  --splitting_cvd_svl                     false
% 2.85/1.00  --splitting_nvd                         32
% 2.85/1.00  --sub_typing                            true
% 2.85/1.00  --prep_gs_sim                           true
% 2.85/1.00  --prep_unflatten                        true
% 2.85/1.00  --prep_res_sim                          true
% 2.85/1.00  --prep_upred                            true
% 2.85/1.00  --prep_sem_filter                       exhaustive
% 2.85/1.00  --prep_sem_filter_out                   false
% 2.85/1.00  --pred_elim                             true
% 2.85/1.00  --res_sim_input                         true
% 2.85/1.00  --eq_ax_congr_red                       true
% 2.85/1.00  --pure_diseq_elim                       true
% 2.85/1.00  --brand_transform                       false
% 2.85/1.00  --non_eq_to_eq                          false
% 2.85/1.00  --prep_def_merge                        true
% 2.85/1.00  --prep_def_merge_prop_impl              false
% 2.85/1.00  --prep_def_merge_mbd                    true
% 2.85/1.00  --prep_def_merge_tr_red                 false
% 2.85/1.00  --prep_def_merge_tr_cl                  false
% 2.85/1.00  --smt_preprocessing                     true
% 2.85/1.00  --smt_ac_axioms                         fast
% 2.85/1.00  --preprocessed_out                      false
% 2.85/1.00  --preprocessed_stats                    false
% 2.85/1.00  
% 2.85/1.00  ------ Abstraction refinement Options
% 2.85/1.00  
% 2.85/1.00  --abstr_ref                             []
% 2.85/1.00  --abstr_ref_prep                        false
% 2.85/1.00  --abstr_ref_until_sat                   false
% 2.85/1.00  --abstr_ref_sig_restrict                funpre
% 2.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/1.00  --abstr_ref_under                       []
% 2.85/1.00  
% 2.85/1.00  ------ SAT Options
% 2.85/1.00  
% 2.85/1.00  --sat_mode                              false
% 2.85/1.00  --sat_fm_restart_options                ""
% 2.85/1.00  --sat_gr_def                            false
% 2.85/1.00  --sat_epr_types                         true
% 2.85/1.00  --sat_non_cyclic_types                  false
% 2.85/1.00  --sat_finite_models                     false
% 2.85/1.00  --sat_fm_lemmas                         false
% 2.85/1.00  --sat_fm_prep                           false
% 2.85/1.00  --sat_fm_uc_incr                        true
% 2.85/1.00  --sat_out_model                         small
% 2.85/1.00  --sat_out_clauses                       false
% 2.85/1.00  
% 2.85/1.00  ------ QBF Options
% 2.85/1.00  
% 2.85/1.00  --qbf_mode                              false
% 2.85/1.00  --qbf_elim_univ                         false
% 2.85/1.00  --qbf_dom_inst                          none
% 2.85/1.00  --qbf_dom_pre_inst                      false
% 2.85/1.00  --qbf_sk_in                             false
% 2.85/1.00  --qbf_pred_elim                         true
% 2.85/1.00  --qbf_split                             512
% 2.85/1.00  
% 2.85/1.00  ------ BMC1 Options
% 2.85/1.00  
% 2.85/1.00  --bmc1_incremental                      false
% 2.85/1.00  --bmc1_axioms                           reachable_all
% 2.85/1.00  --bmc1_min_bound                        0
% 2.85/1.00  --bmc1_max_bound                        -1
% 2.85/1.00  --bmc1_max_bound_default                -1
% 2.85/1.00  --bmc1_symbol_reachability              true
% 2.85/1.00  --bmc1_property_lemmas                  false
% 2.85/1.00  --bmc1_k_induction                      false
% 2.85/1.00  --bmc1_non_equiv_states                 false
% 2.85/1.00  --bmc1_deadlock                         false
% 2.85/1.00  --bmc1_ucm                              false
% 2.85/1.00  --bmc1_add_unsat_core                   none
% 2.85/1.00  --bmc1_unsat_core_children              false
% 2.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/1.00  --bmc1_out_stat                         full
% 2.85/1.00  --bmc1_ground_init                      false
% 2.85/1.00  --bmc1_pre_inst_next_state              false
% 2.85/1.00  --bmc1_pre_inst_state                   false
% 2.85/1.00  --bmc1_pre_inst_reach_state             false
% 2.85/1.00  --bmc1_out_unsat_core                   false
% 2.85/1.00  --bmc1_aig_witness_out                  false
% 2.85/1.00  --bmc1_verbose                          false
% 2.85/1.00  --bmc1_dump_clauses_tptp                false
% 2.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.85/1.00  --bmc1_dump_file                        -
% 2.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.85/1.00  --bmc1_ucm_extend_mode                  1
% 2.85/1.00  --bmc1_ucm_init_mode                    2
% 2.85/1.00  --bmc1_ucm_cone_mode                    none
% 2.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.85/1.00  --bmc1_ucm_relax_model                  4
% 2.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/1.00  --bmc1_ucm_layered_model                none
% 2.85/1.00  --bmc1_ucm_max_lemma_size               10
% 2.85/1.00  
% 2.85/1.00  ------ AIG Options
% 2.85/1.00  
% 2.85/1.00  --aig_mode                              false
% 2.85/1.00  
% 2.85/1.00  ------ Instantiation Options
% 2.85/1.00  
% 2.85/1.00  --instantiation_flag                    true
% 2.85/1.00  --inst_sos_flag                         false
% 2.85/1.00  --inst_sos_phase                        true
% 2.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/1.00  --inst_lit_sel_side                     num_symb
% 2.85/1.00  --inst_solver_per_active                1400
% 2.85/1.00  --inst_solver_calls_frac                1.
% 2.85/1.00  --inst_passive_queue_type               priority_queues
% 2.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/1.00  --inst_passive_queues_freq              [25;2]
% 2.85/1.00  --inst_dismatching                      true
% 2.85/1.00  --inst_eager_unprocessed_to_passive     true
% 2.85/1.00  --inst_prop_sim_given                   true
% 2.85/1.00  --inst_prop_sim_new                     false
% 2.85/1.00  --inst_subs_new                         false
% 2.85/1.00  --inst_eq_res_simp                      false
% 2.85/1.00  --inst_subs_given                       false
% 2.85/1.00  --inst_orphan_elimination               true
% 2.85/1.00  --inst_learning_loop_flag               true
% 2.85/1.00  --inst_learning_start                   3000
% 2.85/1.00  --inst_learning_factor                  2
% 2.85/1.00  --inst_start_prop_sim_after_learn       3
% 2.85/1.00  --inst_sel_renew                        solver
% 2.85/1.00  --inst_lit_activity_flag                true
% 2.85/1.00  --inst_restr_to_given                   false
% 2.85/1.00  --inst_activity_threshold               500
% 2.85/1.00  --inst_out_proof                        true
% 2.85/1.00  
% 2.85/1.00  ------ Resolution Options
% 2.85/1.00  
% 2.85/1.00  --resolution_flag                       true
% 2.85/1.00  --res_lit_sel                           adaptive
% 2.85/1.00  --res_lit_sel_side                      none
% 2.85/1.00  --res_ordering                          kbo
% 2.85/1.00  --res_to_prop_solver                    active
% 2.85/1.00  --res_prop_simpl_new                    false
% 2.85/1.00  --res_prop_simpl_given                  true
% 2.85/1.00  --res_passive_queue_type                priority_queues
% 2.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/1.00  --res_passive_queues_freq               [15;5]
% 2.85/1.00  --res_forward_subs                      full
% 2.85/1.00  --res_backward_subs                     full
% 2.85/1.00  --res_forward_subs_resolution           true
% 2.85/1.00  --res_backward_subs_resolution          true
% 2.85/1.00  --res_orphan_elimination                true
% 2.85/1.00  --res_time_limit                        2.
% 2.85/1.00  --res_out_proof                         true
% 2.85/1.00  
% 2.85/1.00  ------ Superposition Options
% 2.85/1.00  
% 2.85/1.00  --superposition_flag                    true
% 2.85/1.00  --sup_passive_queue_type                priority_queues
% 2.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.85/1.00  --demod_completeness_check              fast
% 2.85/1.00  --demod_use_ground                      true
% 2.85/1.00  --sup_to_prop_solver                    passive
% 2.85/1.00  --sup_prop_simpl_new                    true
% 2.85/1.00  --sup_prop_simpl_given                  true
% 2.85/1.00  --sup_fun_splitting                     false
% 2.85/1.00  --sup_smt_interval                      50000
% 2.85/1.00  
% 2.85/1.00  ------ Superposition Simplification Setup
% 2.85/1.00  
% 2.85/1.00  --sup_indices_passive                   []
% 2.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_full_bw                           [BwDemod]
% 2.85/1.00  --sup_immed_triv                        [TrivRules]
% 2.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_immed_bw_main                     []
% 2.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.00  
% 2.85/1.00  ------ Combination Options
% 2.85/1.00  
% 2.85/1.00  --comb_res_mult                         3
% 2.85/1.00  --comb_sup_mult                         2
% 2.85/1.00  --comb_inst_mult                        10
% 2.85/1.00  
% 2.85/1.00  ------ Debug Options
% 2.85/1.00  
% 2.85/1.00  --dbg_backtrace                         false
% 2.85/1.00  --dbg_dump_prop_clauses                 false
% 2.85/1.00  --dbg_dump_prop_clauses_file            -
% 2.85/1.00  --dbg_out_stat                          false
% 2.85/1.00  ------ Parsing...
% 2.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/1.00  ------ Proving...
% 2.85/1.00  ------ Problem Properties 
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  clauses                                 30
% 2.85/1.00  conjectures                             5
% 2.85/1.00  EPR                                     2
% 2.85/1.00  Horn                                    30
% 2.85/1.00  unary                                   14
% 2.85/1.00  binary                                  1
% 2.85/1.00  lits                                    91
% 2.85/1.00  lits eq                                 18
% 2.85/1.00  fd_pure                                 0
% 2.85/1.00  fd_pseudo                               0
% 2.85/1.00  fd_cond                                 0
% 2.85/1.00  fd_pseudo_cond                          1
% 2.85/1.00  AC symbols                              0
% 2.85/1.00  
% 2.85/1.00  ------ Schedule dynamic 5 is on 
% 2.85/1.00  
% 2.85/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  ------ 
% 2.85/1.00  Current options:
% 2.85/1.00  ------ 
% 2.85/1.00  
% 2.85/1.00  ------ Input Options
% 2.85/1.00  
% 2.85/1.00  --out_options                           all
% 2.85/1.00  --tptp_safe_out                         true
% 2.85/1.00  --problem_path                          ""
% 2.85/1.00  --include_path                          ""
% 2.85/1.00  --clausifier                            res/vclausify_rel
% 2.85/1.00  --clausifier_options                    --mode clausify
% 2.85/1.00  --stdin                                 false
% 2.85/1.00  --stats_out                             all
% 2.85/1.00  
% 2.85/1.00  ------ General Options
% 2.85/1.00  
% 2.85/1.00  --fof                                   false
% 2.85/1.00  --time_out_real                         305.
% 2.85/1.00  --time_out_virtual                      -1.
% 2.85/1.00  --symbol_type_check                     false
% 2.85/1.00  --clausify_out                          false
% 2.85/1.00  --sig_cnt_out                           false
% 2.85/1.00  --trig_cnt_out                          false
% 2.85/1.00  --trig_cnt_out_tolerance                1.
% 2.85/1.00  --trig_cnt_out_sk_spl                   false
% 2.85/1.00  --abstr_cl_out                          false
% 2.85/1.00  
% 2.85/1.00  ------ Global Options
% 2.85/1.00  
% 2.85/1.00  --schedule                              default
% 2.85/1.00  --add_important_lit                     false
% 2.85/1.00  --prop_solver_per_cl                    1000
% 2.85/1.00  --min_unsat_core                        false
% 2.85/1.00  --soft_assumptions                      false
% 2.85/1.00  --soft_lemma_size                       3
% 2.85/1.00  --prop_impl_unit_size                   0
% 2.85/1.00  --prop_impl_unit                        []
% 2.85/1.00  --share_sel_clauses                     true
% 2.85/1.00  --reset_solvers                         false
% 2.85/1.00  --bc_imp_inh                            [conj_cone]
% 2.85/1.00  --conj_cone_tolerance                   3.
% 2.85/1.00  --extra_neg_conj                        none
% 2.85/1.00  --large_theory_mode                     true
% 2.85/1.00  --prolific_symb_bound                   200
% 2.85/1.00  --lt_threshold                          2000
% 2.85/1.00  --clause_weak_htbl                      true
% 2.85/1.00  --gc_record_bc_elim                     false
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing Options
% 2.85/1.00  
% 2.85/1.00  --preprocessing_flag                    true
% 2.85/1.00  --time_out_prep_mult                    0.1
% 2.85/1.00  --splitting_mode                        input
% 2.85/1.00  --splitting_grd                         true
% 2.85/1.00  --splitting_cvd                         false
% 2.85/1.00  --splitting_cvd_svl                     false
% 2.85/1.00  --splitting_nvd                         32
% 2.85/1.00  --sub_typing                            true
% 2.85/1.00  --prep_gs_sim                           true
% 2.85/1.00  --prep_unflatten                        true
% 2.85/1.00  --prep_res_sim                          true
% 2.85/1.00  --prep_upred                            true
% 2.85/1.00  --prep_sem_filter                       exhaustive
% 2.85/1.00  --prep_sem_filter_out                   false
% 2.85/1.00  --pred_elim                             true
% 2.85/1.00  --res_sim_input                         true
% 2.85/1.00  --eq_ax_congr_red                       true
% 2.85/1.00  --pure_diseq_elim                       true
% 2.85/1.00  --brand_transform                       false
% 2.85/1.00  --non_eq_to_eq                          false
% 2.85/1.00  --prep_def_merge                        true
% 2.85/1.00  --prep_def_merge_prop_impl              false
% 2.85/1.00  --prep_def_merge_mbd                    true
% 2.85/1.00  --prep_def_merge_tr_red                 false
% 2.85/1.00  --prep_def_merge_tr_cl                  false
% 2.85/1.00  --smt_preprocessing                     true
% 2.85/1.00  --smt_ac_axioms                         fast
% 2.85/1.00  --preprocessed_out                      false
% 2.85/1.00  --preprocessed_stats                    false
% 2.85/1.00  
% 2.85/1.00  ------ Abstraction refinement Options
% 2.85/1.00  
% 2.85/1.00  --abstr_ref                             []
% 2.85/1.00  --abstr_ref_prep                        false
% 2.85/1.00  --abstr_ref_until_sat                   false
% 2.85/1.00  --abstr_ref_sig_restrict                funpre
% 2.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/1.00  --abstr_ref_under                       []
% 2.85/1.00  
% 2.85/1.00  ------ SAT Options
% 2.85/1.00  
% 2.85/1.00  --sat_mode                              false
% 2.85/1.00  --sat_fm_restart_options                ""
% 2.85/1.00  --sat_gr_def                            false
% 2.85/1.00  --sat_epr_types                         true
% 2.85/1.00  --sat_non_cyclic_types                  false
% 2.85/1.00  --sat_finite_models                     false
% 2.85/1.00  --sat_fm_lemmas                         false
% 2.85/1.00  --sat_fm_prep                           false
% 2.85/1.00  --sat_fm_uc_incr                        true
% 2.85/1.00  --sat_out_model                         small
% 2.85/1.00  --sat_out_clauses                       false
% 2.85/1.00  
% 2.85/1.00  ------ QBF Options
% 2.85/1.00  
% 2.85/1.00  --qbf_mode                              false
% 2.85/1.00  --qbf_elim_univ                         false
% 2.85/1.00  --qbf_dom_inst                          none
% 2.85/1.00  --qbf_dom_pre_inst                      false
% 2.85/1.00  --qbf_sk_in                             false
% 2.85/1.00  --qbf_pred_elim                         true
% 2.85/1.00  --qbf_split                             512
% 2.85/1.00  
% 2.85/1.00  ------ BMC1 Options
% 2.85/1.00  
% 2.85/1.00  --bmc1_incremental                      false
% 2.85/1.00  --bmc1_axioms                           reachable_all
% 2.85/1.00  --bmc1_min_bound                        0
% 2.85/1.00  --bmc1_max_bound                        -1
% 2.85/1.00  --bmc1_max_bound_default                -1
% 2.85/1.00  --bmc1_symbol_reachability              true
% 2.85/1.00  --bmc1_property_lemmas                  false
% 2.85/1.00  --bmc1_k_induction                      false
% 2.85/1.00  --bmc1_non_equiv_states                 false
% 2.85/1.00  --bmc1_deadlock                         false
% 2.85/1.00  --bmc1_ucm                              false
% 2.85/1.00  --bmc1_add_unsat_core                   none
% 2.85/1.00  --bmc1_unsat_core_children              false
% 2.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/1.00  --bmc1_out_stat                         full
% 2.85/1.00  --bmc1_ground_init                      false
% 2.85/1.00  --bmc1_pre_inst_next_state              false
% 2.85/1.00  --bmc1_pre_inst_state                   false
% 2.85/1.00  --bmc1_pre_inst_reach_state             false
% 2.85/1.00  --bmc1_out_unsat_core                   false
% 2.85/1.00  --bmc1_aig_witness_out                  false
% 2.85/1.00  --bmc1_verbose                          false
% 2.85/1.00  --bmc1_dump_clauses_tptp                false
% 2.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.85/1.00  --bmc1_dump_file                        -
% 2.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.85/1.00  --bmc1_ucm_extend_mode                  1
% 2.85/1.00  --bmc1_ucm_init_mode                    2
% 2.85/1.00  --bmc1_ucm_cone_mode                    none
% 2.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.85/1.00  --bmc1_ucm_relax_model                  4
% 2.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/1.00  --bmc1_ucm_layered_model                none
% 2.85/1.00  --bmc1_ucm_max_lemma_size               10
% 2.85/1.00  
% 2.85/1.00  ------ AIG Options
% 2.85/1.00  
% 2.85/1.00  --aig_mode                              false
% 2.85/1.00  
% 2.85/1.00  ------ Instantiation Options
% 2.85/1.00  
% 2.85/1.00  --instantiation_flag                    true
% 2.85/1.00  --inst_sos_flag                         false
% 2.85/1.00  --inst_sos_phase                        true
% 2.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/1.00  --inst_lit_sel_side                     none
% 2.85/1.00  --inst_solver_per_active                1400
% 2.85/1.00  --inst_solver_calls_frac                1.
% 2.85/1.00  --inst_passive_queue_type               priority_queues
% 2.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/1.00  --inst_passive_queues_freq              [25;2]
% 2.85/1.00  --inst_dismatching                      true
% 2.85/1.00  --inst_eager_unprocessed_to_passive     true
% 2.85/1.00  --inst_prop_sim_given                   true
% 2.85/1.00  --inst_prop_sim_new                     false
% 2.85/1.00  --inst_subs_new                         false
% 2.85/1.00  --inst_eq_res_simp                      false
% 2.85/1.00  --inst_subs_given                       false
% 2.85/1.00  --inst_orphan_elimination               true
% 2.85/1.00  --inst_learning_loop_flag               true
% 2.85/1.00  --inst_learning_start                   3000
% 2.85/1.00  --inst_learning_factor                  2
% 2.85/1.00  --inst_start_prop_sim_after_learn       3
% 2.85/1.00  --inst_sel_renew                        solver
% 2.85/1.00  --inst_lit_activity_flag                true
% 2.85/1.00  --inst_restr_to_given                   false
% 2.85/1.00  --inst_activity_threshold               500
% 2.85/1.00  --inst_out_proof                        true
% 2.85/1.00  
% 2.85/1.00  ------ Resolution Options
% 2.85/1.00  
% 2.85/1.00  --resolution_flag                       false
% 2.85/1.00  --res_lit_sel                           adaptive
% 2.85/1.00  --res_lit_sel_side                      none
% 2.85/1.00  --res_ordering                          kbo
% 2.85/1.00  --res_to_prop_solver                    active
% 2.85/1.00  --res_prop_simpl_new                    false
% 2.85/1.00  --res_prop_simpl_given                  true
% 2.85/1.00  --res_passive_queue_type                priority_queues
% 2.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/1.00  --res_passive_queues_freq               [15;5]
% 2.85/1.00  --res_forward_subs                      full
% 2.85/1.00  --res_backward_subs                     full
% 2.85/1.00  --res_forward_subs_resolution           true
% 2.85/1.00  --res_backward_subs_resolution          true
% 2.85/1.00  --res_orphan_elimination                true
% 2.85/1.00  --res_time_limit                        2.
% 2.85/1.00  --res_out_proof                         true
% 2.85/1.00  
% 2.85/1.00  ------ Superposition Options
% 2.85/1.00  
% 2.85/1.00  --superposition_flag                    true
% 2.85/1.00  --sup_passive_queue_type                priority_queues
% 2.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.85/1.00  --demod_completeness_check              fast
% 2.85/1.00  --demod_use_ground                      true
% 2.85/1.00  --sup_to_prop_solver                    passive
% 2.85/1.00  --sup_prop_simpl_new                    true
% 2.85/1.00  --sup_prop_simpl_given                  true
% 2.85/1.00  --sup_fun_splitting                     false
% 2.85/1.00  --sup_smt_interval                      50000
% 2.85/1.00  
% 2.85/1.00  ------ Superposition Simplification Setup
% 2.85/1.00  
% 2.85/1.00  --sup_indices_passive                   []
% 2.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_full_bw                           [BwDemod]
% 2.85/1.00  --sup_immed_triv                        [TrivRules]
% 2.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_immed_bw_main                     []
% 2.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.00  
% 2.85/1.00  ------ Combination Options
% 2.85/1.00  
% 2.85/1.00  --comb_res_mult                         3
% 2.85/1.00  --comb_sup_mult                         2
% 2.85/1.00  --comb_inst_mult                        10
% 2.85/1.00  
% 2.85/1.00  ------ Debug Options
% 2.85/1.00  
% 2.85/1.00  --dbg_backtrace                         false
% 2.85/1.00  --dbg_dump_prop_clauses                 false
% 2.85/1.00  --dbg_dump_prop_clauses_file            -
% 2.85/1.00  --dbg_out_stat                          false
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  ------ Proving...
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  % SZS status Theorem for theBenchmark.p
% 2.85/1.00  
% 2.85/1.00   Resolution empty clause
% 2.85/1.00  
% 2.85/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/1.00  
% 2.85/1.00  fof(f18,conjecture,(
% 2.85/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f19,negated_conjecture,(
% 2.85/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.85/1.00    inference(negated_conjecture,[],[f18])).
% 2.85/1.00  
% 2.85/1.00  fof(f46,plain,(
% 2.85/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.85/1.00    inference(ennf_transformation,[],[f19])).
% 2.85/1.00  
% 2.85/1.00  fof(f47,plain,(
% 2.85/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.85/1.00    inference(flattening,[],[f46])).
% 2.85/1.00  
% 2.85/1.00  fof(f53,plain,(
% 2.85/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.85/1.00    introduced(choice_axiom,[])).
% 2.85/1.00  
% 2.85/1.00  fof(f52,plain,(
% 2.85/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))) )),
% 2.85/1.00    introduced(choice_axiom,[])).
% 2.85/1.00  
% 2.85/1.00  fof(f51,plain,(
% 2.85/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK1))),
% 2.85/1.00    introduced(choice_axiom,[])).
% 2.85/1.00  
% 2.85/1.00  fof(f54,plain,(
% 2.85/1.00    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK1)),
% 2.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53,f52,f51])).
% 2.85/1.00  
% 2.85/1.00  fof(f89,plain,(
% 2.85/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f15,axiom,(
% 2.85/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f41,plain,(
% 2.85/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.85/1.00    inference(ennf_transformation,[],[f15])).
% 2.85/1.00  
% 2.85/1.00  fof(f81,plain,(
% 2.85/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f41])).
% 2.85/1.00  
% 2.85/1.00  fof(f86,plain,(
% 2.85/1.00    l1_struct_0(sK2)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f84,plain,(
% 2.85/1.00    l1_struct_0(sK1)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f1,axiom,(
% 2.85/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f22,plain,(
% 2.85/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.85/1.00    inference(ennf_transformation,[],[f1])).
% 2.85/1.00  
% 2.85/1.00  fof(f55,plain,(
% 2.85/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f22])).
% 2.85/1.00  
% 2.85/1.00  fof(f2,axiom,(
% 2.85/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f56,plain,(
% 2.85/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.85/1.00    inference(cnf_transformation,[],[f2])).
% 2.85/1.00  
% 2.85/1.00  fof(f10,axiom,(
% 2.85/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f33,plain,(
% 2.85/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.85/1.00    inference(ennf_transformation,[],[f10])).
% 2.85/1.00  
% 2.85/1.00  fof(f34,plain,(
% 2.85/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.85/1.00    inference(flattening,[],[f33])).
% 2.85/1.00  
% 2.85/1.00  fof(f69,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f34])).
% 2.85/1.00  
% 2.85/1.00  fof(f16,axiom,(
% 2.85/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f42,plain,(
% 2.85/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.85/1.00    inference(ennf_transformation,[],[f16])).
% 2.85/1.00  
% 2.85/1.00  fof(f43,plain,(
% 2.85/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.85/1.00    inference(flattening,[],[f42])).
% 2.85/1.00  
% 2.85/1.00  fof(f82,plain,(
% 2.85/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f43])).
% 2.85/1.00  
% 2.85/1.00  fof(f85,plain,(
% 2.85/1.00    ~v2_struct_0(sK2)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f11,axiom,(
% 2.85/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f35,plain,(
% 2.85/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.85/1.00    inference(ennf_transformation,[],[f11])).
% 2.85/1.00  
% 2.85/1.00  fof(f36,plain,(
% 2.85/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.85/1.00    inference(flattening,[],[f35])).
% 2.85/1.00  
% 2.85/1.00  fof(f48,plain,(
% 2.85/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.85/1.00    inference(nnf_transformation,[],[f36])).
% 2.85/1.00  
% 2.85/1.00  fof(f70,plain,(
% 2.85/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f48])).
% 2.85/1.00  
% 2.85/1.00  fof(f8,axiom,(
% 2.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f21,plain,(
% 2.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.85/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.85/1.00  
% 2.85/1.00  fof(f31,plain,(
% 2.85/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/1.00    inference(ennf_transformation,[],[f21])).
% 2.85/1.00  
% 2.85/1.00  fof(f66,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/1.00    inference(cnf_transformation,[],[f31])).
% 2.85/1.00  
% 2.85/1.00  fof(f87,plain,(
% 2.85/1.00    v1_funct_1(sK3)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f88,plain,(
% 2.85/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f9,axiom,(
% 2.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f32,plain,(
% 2.85/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/1.00    inference(ennf_transformation,[],[f9])).
% 2.85/1.00  
% 2.85/1.00  fof(f67,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/1.00    inference(cnf_transformation,[],[f32])).
% 2.85/1.00  
% 2.85/1.00  fof(f90,plain,(
% 2.85/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f13,axiom,(
% 2.85/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f37,plain,(
% 2.85/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.85/1.00    inference(ennf_transformation,[],[f13])).
% 2.85/1.00  
% 2.85/1.00  fof(f38,plain,(
% 2.85/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.85/1.00    inference(flattening,[],[f37])).
% 2.85/1.00  
% 2.85/1.00  fof(f77,plain,(
% 2.85/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f38])).
% 2.85/1.00  
% 2.85/1.00  fof(f92,plain,(
% 2.85/1.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f17,axiom,(
% 2.85/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f44,plain,(
% 2.85/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.85/1.00    inference(ennf_transformation,[],[f17])).
% 2.85/1.00  
% 2.85/1.00  fof(f45,plain,(
% 2.85/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.85/1.00    inference(flattening,[],[f44])).
% 2.85/1.00  
% 2.85/1.00  fof(f83,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f45])).
% 2.85/1.00  
% 2.85/1.00  fof(f91,plain,(
% 2.85/1.00    v2_funct_1(sK3)),
% 2.85/1.00    inference(cnf_transformation,[],[f54])).
% 2.85/1.00  
% 2.85/1.00  fof(f5,axiom,(
% 2.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f25,plain,(
% 2.85/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/1.00    inference(ennf_transformation,[],[f5])).
% 2.85/1.00  
% 2.85/1.00  fof(f26,plain,(
% 2.85/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/1.00    inference(flattening,[],[f25])).
% 2.85/1.00  
% 2.85/1.00  fof(f61,plain,(
% 2.85/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f26])).
% 2.85/1.00  
% 2.85/1.00  fof(f6,axiom,(
% 2.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f27,plain,(
% 2.85/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/1.00    inference(ennf_transformation,[],[f6])).
% 2.85/1.00  
% 2.85/1.00  fof(f28,plain,(
% 2.85/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/1.00    inference(flattening,[],[f27])).
% 2.85/1.00  
% 2.85/1.00  fof(f63,plain,(
% 2.85/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f28])).
% 2.85/1.00  
% 2.85/1.00  fof(f14,axiom,(
% 2.85/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f39,plain,(
% 2.85/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.85/1.00    inference(ennf_transformation,[],[f14])).
% 2.85/1.00  
% 2.85/1.00  fof(f40,plain,(
% 2.85/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.85/1.00    inference(flattening,[],[f39])).
% 2.85/1.00  
% 2.85/1.00  fof(f78,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f40])).
% 2.85/1.00  
% 2.85/1.00  fof(f80,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f40])).
% 2.85/1.00  
% 2.85/1.00  fof(f4,axiom,(
% 2.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f23,plain,(
% 2.85/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/1.00    inference(ennf_transformation,[],[f4])).
% 2.85/1.00  
% 2.85/1.00  fof(f24,plain,(
% 2.85/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/1.00    inference(flattening,[],[f23])).
% 2.85/1.00  
% 2.85/1.00  fof(f60,plain,(
% 2.85/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f24])).
% 2.85/1.00  
% 2.85/1.00  fof(f3,axiom,(
% 2.85/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f58,plain,(
% 2.85/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.85/1.00    inference(cnf_transformation,[],[f3])).
% 2.85/1.00  
% 2.85/1.00  fof(f79,plain,(
% 2.85/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f40])).
% 2.85/1.00  
% 2.85/1.00  fof(f62,plain,(
% 2.85/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f26])).
% 2.85/1.00  
% 2.85/1.00  fof(f7,axiom,(
% 2.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.00  
% 2.85/1.00  fof(f29,plain,(
% 2.85/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/1.00    inference(ennf_transformation,[],[f7])).
% 2.85/1.00  
% 2.85/1.00  fof(f30,plain,(
% 2.85/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/1.00    inference(flattening,[],[f29])).
% 2.85/1.00  
% 2.85/1.00  fof(f65,plain,(
% 2.85/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/1.00    inference(cnf_transformation,[],[f30])).
% 2.85/1.00  
% 2.85/1.00  cnf(c_32,negated_conjecture,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.85/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1192,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_26,plain,
% 2.85/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_35,negated_conjecture,
% 2.85/1.00      ( l1_struct_0(sK2) ),
% 2.85/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_422,plain,
% 2.85/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_423,plain,
% 2.85/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_37,negated_conjecture,
% 2.85/1.00      ( l1_struct_0(sK1) ),
% 2.85/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_427,plain,
% 2.85/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_428,plain,
% 2.85/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1240,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1192,c_423,c_428]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_0,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1213,plain,
% 2.85/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.85/1.00      | v1_relat_1(X1) != iProver_top
% 2.85/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1990,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1240,c_1213]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_43,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1479,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | v1_relat_1(X0)
% 2.85/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1792,plain,
% 2.85/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 2.85/1.00      | v1_relat_1(sK3) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1479]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1793,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1853,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1854,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3113,plain,
% 2.85/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_1990,c_43,c_1793,c_1854]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_13,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | v1_partfun1(X0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | v1_xboole_0(X2)
% 2.85/1.00      | ~ v1_funct_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_27,plain,
% 2.85/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_36,negated_conjecture,
% 2.85/1.00      ( ~ v2_struct_0(sK2) ),
% 2.85/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_409,plain,
% 2.85/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_410,plain,
% 2.85/1.00      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_50,plain,
% 2.85/1.00      ( v2_struct_0(sK2)
% 2.85/1.00      | ~ l1_struct_0(sK2)
% 2.85/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_412,plain,
% 2.85/1.00      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_410,c_36,c_35,c_50]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_434,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | v1_partfun1(X0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | u1_struct_0(sK2) != X2 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_412]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_435,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
% 2.85/1.00      | v1_partfun1(X0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(X0) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_16,plain,
% 2.85/1.00      ( ~ v1_partfun1(X0,X1)
% 2.85/1.00      | ~ v4_relat_1(X0,X1)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k1_relat_1(X0) = X1 ),
% 2.85/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_492,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
% 2.85/1.00      | ~ v4_relat_1(X0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k1_relat_1(X0) = X1 ),
% 2.85/1.00      inference(resolution,[status(thm)],[c_435,c_16]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_11,plain,
% 2.85/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.85/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_508,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k1_relat_1(X0) = X1 ),
% 2.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_492,c_11]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1187,plain,
% 2.85/1.00      ( k1_relat_1(X0) = X1
% 2.85/1.00      | v1_funct_2(X0,X1,u1_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1304,plain,
% 2.85/1.00      ( k1_relat_1(X0) = X1
% 2.85/1.00      | v1_funct_2(X0,X1,k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1187,c_423]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1743,plain,
% 2.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 2.85/1.00      | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1240,c_1304]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_34,negated_conjecture,
% 2.85/1.00      ( v1_funct_1(sK3) ),
% 2.85/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_41,plain,
% 2.85/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_33,negated_conjecture,
% 2.85/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1191,plain,
% 2.85/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1232,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1191,c_423,c_428]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1811,plain,
% 2.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3) | v1_relat_1(sK3) != iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_1743,c_41,c_1232]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3118,plain,
% 2.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_3113,c_1811]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_12,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1202,plain,
% 2.85/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1979,plain,
% 2.85/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1240,c_1202]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_31,negated_conjecture,
% 2.85/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 2.85/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1237,plain,
% 2.85/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_31,c_423,c_428]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2393,plain,
% 2.85/1.00      ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_1979,c_1237]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_22,plain,
% 2.85/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.85/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.85/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.85/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.85/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.85/1.00      | ~ v1_funct_1(X2)
% 2.85/1.00      | ~ v1_funct_1(X3) ),
% 2.85/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_29,negated_conjecture,
% 2.85/1.00      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
% 2.85/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_457,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | ~ v1_funct_2(X3,X1,X2)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X3)
% 2.85/1.00      | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
% 2.85/1.00      | u1_struct_0(sK2) != X2
% 2.85/1.00      | u1_struct_0(sK1) != X1
% 2.85/1.00      | sK3 != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_458,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 2.85/1.00      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_457]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_702,plain,
% 2.85/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 2.85/1.00      | sP0_iProver_split
% 2.85/1.00      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 2.85/1.00      inference(splitting,
% 2.85/1.00                [splitting(split),new_symbols(definition,[])],
% 2.85/1.00                [c_458]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1188,plain,
% 2.85/1.00      ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
% 2.85/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
% 2.85/1.00      | sP0_iProver_split = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1391,plain,
% 2.85/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 2.85/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
% 2.85/1.00      | sP0_iProver_split = iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1188,c_423,c_428]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_701,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ sP0_iProver_split ),
% 2.85/1.00      inference(splitting,
% 2.85/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.85/1.00                [c_458]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1189,plain,
% 2.85/1.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | sP0_iProver_split != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1295,plain,
% 2.85/1.00      ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | sP0_iProver_split != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1189,c_423,c_428]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1397,plain,
% 2.85/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 2.85/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
% 2.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1391,c_1295]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_28,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.85/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.85/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1194,plain,
% 2.85/1.00      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 2.85/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.85/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.85/1.00      | v1_funct_1(X2) != iProver_top
% 2.85/1.00      | v2_funct_1(X2) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1674,plain,
% 2.85/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
% 2.85/1.00      | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1237,c_1194]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_30,negated_conjecture,
% 2.85/1.00      ( v2_funct_1(sK3) ),
% 2.85/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_44,plain,
% 2.85/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1782,plain,
% 2.85/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_1674,c_41,c_44,c_1232,c_1240]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1818,plain,
% 2.85/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 2.85/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1397,c_1782]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2430,plain,
% 2.85/1.00      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 2.85/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_2393,c_1818]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3865,plain,
% 2.85/1.00      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
% 2.85/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3118,c_2430]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_42,plain,
% 2.85/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_53,plain,
% 2.85/1.00      ( ~ l1_struct_0(sK2) | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_7,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1547,plain,
% 2.85/1.00      ( ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_9,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1571,plain,
% 2.85/1.00      ( ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_25,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.85/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1632,plain,
% 2.85/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 2.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3))
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | k2_relset_1(X0,X1,sK3) != X1 ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1697,plain,
% 2.85/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3))
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1632]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1698,plain,
% 2.85/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 2.85/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_23,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.85/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1642,plain,
% 2.85/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | k2_relset_1(X0,X1,sK3) != X1 ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1700,plain,
% 2.85/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1701,plain,
% 2.85/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 2.85/1.00      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1700]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_705,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1733,plain,
% 2.85/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
% 2.85/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.85/1.00      | u1_struct_0(sK2) != X0 ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_705]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1856,plain,
% 2.85/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.85/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
% 2.85/1.00      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1733]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_711,plain,
% 2.85/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.85/1.00      theory(equality) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1491,plain,
% 2.85/1.00      ( v2_funct_1(X0) | ~ v2_funct_1(k6_relat_1(X1)) | X0 != k6_relat_1(X1) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_711]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2034,plain,
% 2.85/1.00      ( v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)))
% 2.85/1.00      | ~ v2_funct_1(k6_relat_1(k1_relat_1(sK3)))
% 2.85/1.00      | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3)) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1491]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2035,plain,
% 2.85/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3))
% 2.85/1.00      | v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) = iProver_top
% 2.85/1.00      | v2_funct_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X1)
% 2.85/1.00      | v2_funct_1(X1)
% 2.85/1.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.85/1.00      | ~ v1_relat_1(X1)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1597,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | v2_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(k5_relat_1(sK3,X0))
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2101,plain,
% 2.85/1.00      ( ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/1.00      | ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)))
% 2.85/1.00      | v2_funct_1(k2_funct_1(sK3))
% 2.85/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1597]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2167,plain,
% 2.85/1.00      ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 2.85/1.00      | v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.85/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2101]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2169,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.85/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 2.85/1.00      | v1_relat_1(k2_funct_1(sK3)) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1479]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2173,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.85/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
% 2.85/1.00      | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2169]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2,plain,
% 2.85/1.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2425,plain,
% 2.85/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK3))) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2426,plain,
% 2.85/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK3))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2425]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2472,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2473,plain,
% 2.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2472]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2434,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_2393,c_1240]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3866,plain,
% 2.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3118,c_2434]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2435,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_2393,c_1232]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3869,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3118,c_2435]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2429,plain,
% 2.85/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_2393,c_1979]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3868,plain,
% 2.85/1.00      ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3118,c_2429]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1197,plain,
% 2.85/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 2.85/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.85/1.00      | v1_funct_1(X2) != iProver_top
% 2.85/1.00      | v2_funct_1(X2) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3997,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_3868,c_1197]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_24,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.85/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1196,plain,
% 2.85/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 2.85/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.85/1.00      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 2.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.85/1.00      | v1_funct_1(X2) != iProver_top
% 2.85/1.00      | v2_funct_1(X2) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3998,plain,
% 2.85/1.00      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.85/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_3868,c_1196]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3126,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_2429,c_1197]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4224,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_3126,c_41,c_44,c_2434,c_2435]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4228,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_4224,c_3118]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4232,plain,
% 2.85/1.00      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_4228,c_1202]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1190,plain,
% 2.85/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_6,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1207,plain,
% 2.85/1.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | v2_funct_1(X0) != iProver_top
% 2.85/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2616,plain,
% 2.85/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1190,c_1207]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1536,plain,
% 2.85/1.00      ( ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2818,plain,
% 2.85/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_2616,c_34,c_32,c_30,c_1536,c_1792,c_1853]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4234,plain,
% 2.85/1.00      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_4232,c_2818]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4339,plain,
% 2.85/1.00      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 2.85/1.00      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.85/1.00      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_4234,c_1194]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_10,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v2_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.85/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1203,plain,
% 2.85/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 2.85/1.00      | v1_funct_1(X0) != iProver_top
% 2.85/1.00      | v2_funct_1(X0) != iProver_top
% 2.85/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2056,plain,
% 2.85/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 2.85/1.00      | v2_funct_1(sK3) != iProver_top
% 2.85/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1190,c_1203]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1555,plain,
% 2.85/1.00      ( ~ v1_funct_1(sK3)
% 2.85/1.00      | ~ v2_funct_1(sK3)
% 2.85/1.00      | ~ v1_relat_1(sK3)
% 2.85/1.00      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2200,plain,
% 2.85/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_2056,c_34,c_32,c_30,c_1555,c_1792,c_1853]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4345,plain,
% 2.85/1.00      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = sK3
% 2.85/1.00      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.85/1.00      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_4339,c_2200]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4568,plain,
% 2.85/1.00      ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_3865,c_35,c_34,c_41,c_42,c_32,c_43,c_31,c_30,c_44,c_53,
% 2.85/1.00                 c_1547,c_1571,c_1698,c_1701,c_1792,c_1793,c_1853,c_1854,
% 2.85/1.00                 c_1856,c_2035,c_2167,c_2173,c_2426,c_2473,c_3866,c_3869,
% 2.85/1.00                 c_3997,c_3998,c_4345]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4452,plain,
% 2.85/1.00      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = sK3 ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_4345,c_35,c_34,c_41,c_42,c_32,c_43,c_31,c_30,c_44,c_53,
% 2.85/1.00                 c_1547,c_1571,c_1698,c_1701,c_1792,c_1793,c_1853,c_1854,
% 2.85/1.00                 c_1856,c_2035,c_2167,c_2173,c_2426,c_2473,c_3866,c_3869,
% 2.85/1.00                 c_3997,c_3998]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4572,plain,
% 2.85/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 2.85/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 2.85/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_4568,c_4452]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4576,plain,
% 2.85/1.00      ( $false ),
% 2.85/1.00      inference(forward_subsumption_resolution,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_4572,c_1190,c_3866,c_3869]) ).
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/1.00  
% 2.85/1.00  ------                               Statistics
% 2.85/1.00  
% 2.85/1.00  ------ General
% 2.85/1.00  
% 2.85/1.00  abstr_ref_over_cycles:                  0
% 2.85/1.00  abstr_ref_under_cycles:                 0
% 2.85/1.00  gc_basic_clause_elim:                   0
% 2.85/1.00  forced_gc_time:                         0
% 2.85/1.00  parsing_time:                           0.011
% 2.85/1.00  unif_index_cands_time:                  0.
% 2.85/1.00  unif_index_add_time:                    0.
% 2.85/1.00  orderings_time:                         0.
% 2.85/1.00  out_proof_time:                         0.017
% 2.85/1.00  total_time:                             0.222
% 2.85/1.00  num_of_symbols:                         58
% 2.85/1.00  num_of_terms:                           3893
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing
% 2.85/1.00  
% 2.85/1.00  num_of_splits:                          1
% 2.85/1.00  num_of_split_atoms:                     1
% 2.85/1.00  num_of_reused_defs:                     0
% 2.85/1.00  num_eq_ax_congr_red:                    7
% 2.85/1.00  num_of_sem_filtered_clauses:            1
% 2.85/1.00  num_of_subtypes:                        0
% 2.85/1.01  monotx_restored_types:                  0
% 2.85/1.01  sat_num_of_epr_types:                   0
% 2.85/1.01  sat_num_of_non_cyclic_types:            0
% 2.85/1.01  sat_guarded_non_collapsed_types:        0
% 2.85/1.01  num_pure_diseq_elim:                    0
% 2.85/1.01  simp_replaced_by:                       0
% 2.85/1.01  res_preprocessed:                       163
% 2.85/1.01  prep_upred:                             0
% 2.85/1.01  prep_unflattend:                        9
% 2.85/1.01  smt_new_axioms:                         0
% 2.85/1.01  pred_elim_cands:                        5
% 2.85/1.01  pred_elim:                              6
% 2.85/1.01  pred_elim_cl:                           8
% 2.85/1.01  pred_elim_cycles:                       8
% 2.85/1.01  merged_defs:                            0
% 2.85/1.01  merged_defs_ncl:                        0
% 2.85/1.01  bin_hyper_res:                          0
% 2.85/1.01  prep_cycles:                            4
% 2.85/1.01  pred_elim_time:                         0.005
% 2.85/1.01  splitting_time:                         0.
% 2.85/1.01  sem_filter_time:                        0.
% 2.85/1.01  monotx_time:                            0.001
% 2.85/1.01  subtype_inf_time:                       0.
% 2.85/1.01  
% 2.85/1.01  ------ Problem properties
% 2.85/1.01  
% 2.85/1.01  clauses:                                30
% 2.85/1.01  conjectures:                            5
% 2.85/1.01  epr:                                    2
% 2.85/1.01  horn:                                   30
% 2.85/1.01  ground:                                 8
% 2.85/1.01  unary:                                  14
% 2.85/1.01  binary:                                 1
% 2.85/1.01  lits:                                   91
% 2.85/1.01  lits_eq:                                18
% 2.85/1.01  fd_pure:                                0
% 2.85/1.01  fd_pseudo:                              0
% 2.85/1.01  fd_cond:                                0
% 2.85/1.01  fd_pseudo_cond:                         1
% 2.85/1.01  ac_symbols:                             0
% 2.85/1.01  
% 2.85/1.01  ------ Propositional Solver
% 2.85/1.01  
% 2.85/1.01  prop_solver_calls:                      29
% 2.85/1.01  prop_fast_solver_calls:                 1284
% 2.85/1.01  smt_solver_calls:                       0
% 2.85/1.01  smt_fast_solver_calls:                  0
% 2.85/1.01  prop_num_of_clauses:                    1551
% 2.85/1.01  prop_preprocess_simplified:             6068
% 2.85/1.01  prop_fo_subsumed:                       70
% 2.85/1.01  prop_solver_time:                       0.
% 2.85/1.01  smt_solver_time:                        0.
% 2.85/1.01  smt_fast_solver_time:                   0.
% 2.85/1.01  prop_fast_solver_time:                  0.
% 2.85/1.01  prop_unsat_core_time:                   0.
% 2.85/1.01  
% 2.85/1.01  ------ QBF
% 2.85/1.01  
% 2.85/1.01  qbf_q_res:                              0
% 2.85/1.01  qbf_num_tautologies:                    0
% 2.85/1.01  qbf_prep_cycles:                        0
% 2.85/1.01  
% 2.85/1.01  ------ BMC1
% 2.85/1.01  
% 2.85/1.01  bmc1_current_bound:                     -1
% 2.85/1.01  bmc1_last_solved_bound:                 -1
% 2.85/1.01  bmc1_unsat_core_size:                   -1
% 2.85/1.01  bmc1_unsat_core_parents_size:           -1
% 2.85/1.01  bmc1_merge_next_fun:                    0
% 2.85/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.85/1.01  
% 2.85/1.01  ------ Instantiation
% 2.85/1.01  
% 2.85/1.01  inst_num_of_clauses:                    532
% 2.85/1.01  inst_num_in_passive:                    70
% 2.85/1.01  inst_num_in_active:                     330
% 2.85/1.01  inst_num_in_unprocessed:                132
% 2.85/1.01  inst_num_of_loops:                      370
% 2.85/1.01  inst_num_of_learning_restarts:          0
% 2.85/1.01  inst_num_moves_active_passive:          36
% 2.85/1.01  inst_lit_activity:                      0
% 2.85/1.01  inst_lit_activity_moves:                0
% 2.85/1.01  inst_num_tautologies:                   0
% 2.85/1.01  inst_num_prop_implied:                  0
% 2.85/1.01  inst_num_existing_simplified:           0
% 2.85/1.01  inst_num_eq_res_simplified:             0
% 2.85/1.01  inst_num_child_elim:                    0
% 2.85/1.01  inst_num_of_dismatching_blockings:      95
% 2.85/1.01  inst_num_of_non_proper_insts:           509
% 2.85/1.01  inst_num_of_duplicates:                 0
% 2.85/1.01  inst_inst_num_from_inst_to_res:         0
% 2.85/1.01  inst_dismatching_checking_time:         0.
% 2.85/1.01  
% 2.85/1.01  ------ Resolution
% 2.85/1.01  
% 2.85/1.01  res_num_of_clauses:                     0
% 2.85/1.01  res_num_in_passive:                     0
% 2.85/1.01  res_num_in_active:                      0
% 2.85/1.01  res_num_of_loops:                       167
% 2.85/1.01  res_forward_subset_subsumed:            90
% 2.85/1.01  res_backward_subset_subsumed:           0
% 2.85/1.01  res_forward_subsumed:                   0
% 2.85/1.01  res_backward_subsumed:                  0
% 2.85/1.01  res_forward_subsumption_resolution:     1
% 2.85/1.01  res_backward_subsumption_resolution:    0
% 2.85/1.01  res_clause_to_clause_subsumption:       109
% 2.85/1.01  res_orphan_elimination:                 0
% 2.85/1.01  res_tautology_del:                      94
% 2.85/1.01  res_num_eq_res_simplified:              0
% 2.85/1.01  res_num_sel_changes:                    0
% 2.85/1.01  res_moves_from_active_to_pass:          0
% 2.85/1.01  
% 2.85/1.01  ------ Superposition
% 2.85/1.01  
% 2.85/1.01  sup_time_total:                         0.
% 2.85/1.01  sup_time_generating:                    0.
% 2.85/1.01  sup_time_sim_full:                      0.
% 2.85/1.01  sup_time_sim_immed:                     0.
% 2.85/1.01  
% 2.85/1.01  sup_num_of_clauses:                     64
% 2.85/1.01  sup_num_in_active:                      56
% 2.85/1.01  sup_num_in_passive:                     8
% 2.85/1.01  sup_num_of_loops:                       72
% 2.85/1.01  sup_fw_superposition:                   31
% 2.85/1.01  sup_bw_superposition:                   32
% 2.85/1.01  sup_immediate_simplified:               24
% 2.85/1.01  sup_given_eliminated:                   0
% 2.85/1.01  comparisons_done:                       0
% 2.85/1.01  comparisons_avoided:                    0
% 2.85/1.01  
% 2.85/1.01  ------ Simplifications
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  sim_fw_subset_subsumed:                 14
% 2.85/1.01  sim_bw_subset_subsumed:                 4
% 2.85/1.01  sim_fw_subsumed:                        3
% 2.85/1.01  sim_bw_subsumed:                        0
% 2.85/1.01  sim_fw_subsumption_res:                 11
% 2.85/1.01  sim_bw_subsumption_res:                 0
% 2.85/1.01  sim_tautology_del:                      0
% 2.85/1.01  sim_eq_tautology_del:                   4
% 2.85/1.01  sim_eq_res_simp:                        0
% 2.85/1.01  sim_fw_demodulated:                     0
% 2.85/1.01  sim_bw_demodulated:                     15
% 2.85/1.01  sim_light_normalised:                   22
% 2.85/1.01  sim_joinable_taut:                      0
% 2.85/1.01  sim_joinable_simp:                      0
% 2.85/1.01  sim_ac_normalised:                      0
% 2.85/1.01  sim_smt_subsumption:                    0
% 2.85/1.01  
%------------------------------------------------------------------------------
