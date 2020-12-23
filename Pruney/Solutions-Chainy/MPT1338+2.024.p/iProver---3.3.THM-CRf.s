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
% DateTime   : Thu Dec  3 12:17:04 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  165 (2441 expanded)
%              Number of clauses        :  106 ( 778 expanded)
%              Number of leaves         :   15 ( 692 expanded)
%              Depth                    :   22
%              Number of atoms          :  535 (16839 expanded)
%              Number of equality atoms :  204 (5855 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_813,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1087,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_278,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_279,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_809,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_279])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_273,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_274,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_810,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_1109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1087,c_809,c_810])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1086,plain,
    ( k2_relset_1(X0_54,X1_54,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_1304,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1109,c_1086])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_814,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1106,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_814,c_809,c_810])).

cnf(c_1349,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1304,c_1106])).

cnf(c_1401,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1349,c_1109])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_260,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_261,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_36,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_263,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_23,c_22,c_36])).

cnf(c_285,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_263])).

cnf(c_286,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_308,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_9])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_9,c_3,c_2])).

cnf(c_313,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_394,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_286,c_313])).

cnf(c_808,plain,
    ( ~ v1_funct_2(X0_51,X0_54,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | k1_relat_1(X0_51) = X0_54 ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1090,plain,
    ( k1_relat_1(X0_51) = X0_54
    | v1_funct_2(X0_51,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1664,plain,
    ( k1_relat_1(X0_51) = X0_54
    | v1_funct_2(X0_51,X0_54,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1090,c_1349])).

cnf(c_1741,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1664])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_812,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1088,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_1103,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1088,c_809,c_810])).

cnf(c_1402,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1349,c_1103])).

cnf(c_1399,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1349,c_1304])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_495,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_21])).

cnf(c_500,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_804,plain,
    ( ~ v1_funct_2(sK2,X0_54,X1_54)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,sK2) != X1_54 ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_1094,plain,
    ( k2_relset_1(X0_54,X1_54,sK2) != X1_54
    | v1_funct_2(sK2,X0_54,X1_54) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_1638,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1094])).

cnf(c_2091,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_1401,c_1402])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k1_relset_1(X0_54,X1_54,X0_51) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1085,plain,
    ( k1_relset_1(X0_54,X1_54,X0_51) = k1_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_2097,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2091,c_1085])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_518,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_519,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_521,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_21])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_521])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_802,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_585])).

cnf(c_1096,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1872,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_19,c_1217])).

cnf(c_2099,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2097,c_1872])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_423,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_21])).

cnf(c_428,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_807,plain,
    ( ~ v1_funct_2(sK2,X0_54,X1_54)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,sK2) != X1_54
    | k2_tops_2(X0_54,X1_54,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_1091,plain,
    ( k2_relset_1(X0_54,X1_54,sK2) != X1_54
    | k2_tops_2(X0_54,X1_54,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_54,X1_54) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_1640,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1091])).

cnf(c_1986,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1640,c_1401,c_1402])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_815,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1128,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_815,c_809,c_810])).

cnf(c_1403,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1349,c_1128])).

cnf(c_1989,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1986,c_1403])).

cnf(c_2197,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2099,c_1989])).

cnf(c_2286,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_2197])).

cnf(c_2096,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2091,c_1086])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_532,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_533,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_535,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_21])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_535])).

cnf(c_573,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_1095,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1868,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1095,c_19,c_1220])).

cnf(c_2102,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2096,c_1868])).

cnf(c_2287,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2286,c_2102])).

cnf(c_2290,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_28,c_1402,c_2287])).

cnf(c_2297,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1401,c_2290])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 1.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/0.98  
% 1.82/0.98  ------  iProver source info
% 1.82/0.98  
% 1.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/0.98  git: non_committed_changes: false
% 1.82/0.98  git: last_make_outside_of_git: false
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     num_symb
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       true
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.98  --res_to_prop_solver                    active
% 1.82/0.98  --res_prop_simpl_new                    false
% 1.82/0.98  --res_prop_simpl_given                  true
% 1.82/0.98  --res_passive_queue_type                priority_queues
% 1.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.98  --res_passive_queues_freq               [15;5]
% 1.82/0.98  --res_forward_subs                      full
% 1.82/0.98  --res_backward_subs                     full
% 1.82/0.98  --res_forward_subs_resolution           true
% 1.82/0.98  --res_backward_subs_resolution          true
% 1.82/0.98  --res_orphan_elimination                true
% 1.82/0.98  --res_time_limit                        2.
% 1.82/0.98  --res_out_proof                         true
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Options
% 1.82/0.98  
% 1.82/0.98  --superposition_flag                    true
% 1.82/0.98  --sup_passive_queue_type                priority_queues
% 1.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.98  --demod_completeness_check              fast
% 1.82/0.98  --demod_use_ground                      true
% 1.82/0.98  --sup_to_prop_solver                    passive
% 1.82/0.98  --sup_prop_simpl_new                    true
% 1.82/0.98  --sup_prop_simpl_given                  true
% 1.82/0.98  --sup_fun_splitting                     false
% 1.82/0.98  --sup_smt_interval                      50000
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Simplification Setup
% 1.82/0.98  
% 1.82/0.98  --sup_indices_passive                   []
% 1.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_full_bw                           [BwDemod]
% 1.82/0.98  --sup_immed_triv                        [TrivRules]
% 1.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_immed_bw_main                     []
% 1.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  
% 1.82/0.98  ------ Combination Options
% 1.82/0.98  
% 1.82/0.98  --comb_res_mult                         3
% 1.82/0.98  --comb_sup_mult                         2
% 1.82/0.98  --comb_inst_mult                        10
% 1.82/0.98  
% 1.82/0.98  ------ Debug Options
% 1.82/0.98  
% 1.82/0.98  --dbg_backtrace                         false
% 1.82/0.98  --dbg_dump_prop_clauses                 false
% 1.82/0.98  --dbg_dump_prop_clauses_file            -
% 1.82/0.98  --dbg_out_stat                          false
% 1.82/0.98  ------ Parsing...
% 1.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.82/0.98  ------ Proving...
% 1.82/0.98  ------ Problem Properties 
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  clauses                                 16
% 1.82/0.98  conjectures                             5
% 1.82/0.98  EPR                                     1
% 1.82/0.98  Horn                                    16
% 1.82/0.98  unary                                   6
% 1.82/0.98  binary                                  5
% 1.82/0.98  lits                                    37
% 1.82/0.98  lits eq                                 15
% 1.82/0.98  fd_pure                                 0
% 1.82/0.98  fd_pseudo                               0
% 1.82/0.98  fd_cond                                 0
% 1.82/0.98  fd_pseudo_cond                          1
% 1.82/0.98  AC symbols                              0
% 1.82/0.98  
% 1.82/0.98  ------ Schedule dynamic 5 is on 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  Current options:
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     none
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       false
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.98  --res_to_prop_solver                    active
% 1.82/0.98  --res_prop_simpl_new                    false
% 1.82/0.98  --res_prop_simpl_given                  true
% 1.82/0.98  --res_passive_queue_type                priority_queues
% 1.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.98  --res_passive_queues_freq               [15;5]
% 1.82/0.98  --res_forward_subs                      full
% 1.82/0.98  --res_backward_subs                     full
% 1.82/0.98  --res_forward_subs_resolution           true
% 1.82/0.98  --res_backward_subs_resolution          true
% 1.82/0.98  --res_orphan_elimination                true
% 1.82/0.98  --res_time_limit                        2.
% 1.82/0.98  --res_out_proof                         true
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Options
% 1.82/0.98  
% 1.82/0.98  --superposition_flag                    true
% 1.82/0.98  --sup_passive_queue_type                priority_queues
% 1.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.98  --demod_completeness_check              fast
% 1.82/0.98  --demod_use_ground                      true
% 1.82/0.98  --sup_to_prop_solver                    passive
% 1.82/0.98  --sup_prop_simpl_new                    true
% 1.82/0.98  --sup_prop_simpl_given                  true
% 1.82/0.98  --sup_fun_splitting                     false
% 1.82/0.98  --sup_smt_interval                      50000
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Simplification Setup
% 1.82/0.98  
% 1.82/0.98  --sup_indices_passive                   []
% 1.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_full_bw                           [BwDemod]
% 1.82/0.98  --sup_immed_triv                        [TrivRules]
% 1.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_immed_bw_main                     []
% 1.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  
% 1.82/0.98  ------ Combination Options
% 1.82/0.98  
% 1.82/0.98  --comb_res_mult                         3
% 1.82/0.98  --comb_sup_mult                         2
% 1.82/0.98  --comb_inst_mult                        10
% 1.82/0.98  
% 1.82/0.98  ------ Debug Options
% 1.82/0.98  
% 1.82/0.98  --dbg_backtrace                         false
% 1.82/0.98  --dbg_dump_prop_clauses                 false
% 1.82/0.98  --dbg_dump_prop_clauses_file            -
% 1.82/0.98  --dbg_out_stat                          false
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  ------ Proving...
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  % SZS status Theorem for theBenchmark.p
% 1.82/0.98  
% 1.82/0.98   Resolution empty clause
% 1.82/0.98  
% 1.82/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  fof(f12,conjecture,(
% 1.82/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f13,negated_conjecture,(
% 1.82/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.82/0.98    inference(negated_conjecture,[],[f12])).
% 1.82/0.98  
% 1.82/0.98  fof(f32,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.82/0.98    inference(ennf_transformation,[],[f13])).
% 1.82/0.98  
% 1.82/0.98  fof(f33,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.82/0.98    inference(flattening,[],[f32])).
% 1.82/0.98  
% 1.82/0.98  fof(f37,plain,(
% 1.82/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f36,plain,(
% 1.82/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f35,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f38,plain,(
% 1.82/0.98    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).
% 1.82/0.98  
% 1.82/0.98  fof(f60,plain,(
% 1.82/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f9,axiom,(
% 1.82/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f27,plain,(
% 1.82/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.82/0.98    inference(ennf_transformation,[],[f9])).
% 1.82/0.98  
% 1.82/0.98  fof(f52,plain,(
% 1.82/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f27])).
% 1.82/0.98  
% 1.82/0.98  fof(f55,plain,(
% 1.82/0.98    l1_struct_0(sK0)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f57,plain,(
% 1.82/0.98    l1_struct_0(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f5,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f20,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.98    inference(ennf_transformation,[],[f5])).
% 1.82/0.98  
% 1.82/0.98  fof(f44,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.98    inference(cnf_transformation,[],[f20])).
% 1.82/0.98  
% 1.82/0.98  fof(f61,plain,(
% 1.82/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f6,axiom,(
% 1.82/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f21,plain,(
% 1.82/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.82/0.98    inference(ennf_transformation,[],[f6])).
% 1.82/0.98  
% 1.82/0.98  fof(f22,plain,(
% 1.82/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.82/0.98    inference(flattening,[],[f21])).
% 1.82/0.98  
% 1.82/0.98  fof(f46,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f22])).
% 1.82/0.98  
% 1.82/0.98  fof(f10,axiom,(
% 1.82/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f28,plain,(
% 1.82/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f10])).
% 1.82/0.98  
% 1.82/0.98  fof(f29,plain,(
% 1.82/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.82/0.98    inference(flattening,[],[f28])).
% 1.82/0.98  
% 1.82/0.98  fof(f53,plain,(
% 1.82/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f29])).
% 1.82/0.98  
% 1.82/0.98  fof(f56,plain,(
% 1.82/0.98    ~v2_struct_0(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f3,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f14,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.82/0.98    inference(pure_predicate_removal,[],[f3])).
% 1.82/0.98  
% 1.82/0.98  fof(f18,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.98    inference(ennf_transformation,[],[f14])).
% 1.82/0.98  
% 1.82/0.98  fof(f42,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.98    inference(cnf_transformation,[],[f18])).
% 1.82/0.98  
% 1.82/0.98  fof(f7,axiom,(
% 1.82/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f23,plain,(
% 1.82/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.82/0.98    inference(ennf_transformation,[],[f7])).
% 1.82/0.98  
% 1.82/0.98  fof(f24,plain,(
% 1.82/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.82/0.98    inference(flattening,[],[f23])).
% 1.82/0.98  
% 1.82/0.98  fof(f34,plain,(
% 1.82/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.82/0.98    inference(nnf_transformation,[],[f24])).
% 1.82/0.98  
% 1.82/0.98  fof(f47,plain,(
% 1.82/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f34])).
% 1.82/0.98  
% 1.82/0.98  fof(f2,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f17,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.98    inference(ennf_transformation,[],[f2])).
% 1.82/0.98  
% 1.82/0.98  fof(f41,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.98    inference(cnf_transformation,[],[f17])).
% 1.82/0.98  
% 1.82/0.98  fof(f58,plain,(
% 1.82/0.98    v1_funct_1(sK2)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f59,plain,(
% 1.82/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f8,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f25,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.82/0.98    inference(ennf_transformation,[],[f8])).
% 1.82/0.98  
% 1.82/0.98  fof(f26,plain,(
% 1.82/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.82/0.98    inference(flattening,[],[f25])).
% 1.82/0.98  
% 1.82/0.98  fof(f51,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f26])).
% 1.82/0.98  
% 1.82/0.98  fof(f62,plain,(
% 1.82/0.98    v2_funct_1(sK2)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f4,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f19,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.98    inference(ennf_transformation,[],[f4])).
% 1.82/0.98  
% 1.82/0.98  fof(f43,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.98    inference(cnf_transformation,[],[f19])).
% 1.82/0.98  
% 1.82/0.98  fof(f1,axiom,(
% 1.82/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f15,plain,(
% 1.82/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f1])).
% 1.82/0.98  
% 1.82/0.98  fof(f16,plain,(
% 1.82/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.82/0.98    inference(flattening,[],[f15])).
% 1.82/0.98  
% 1.82/0.98  fof(f39,plain,(
% 1.82/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f16])).
% 1.82/0.98  
% 1.82/0.98  fof(f11,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f30,plain,(
% 1.82/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.82/0.98    inference(ennf_transformation,[],[f11])).
% 1.82/0.98  
% 1.82/0.98  fof(f31,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.82/0.98    inference(flattening,[],[f30])).
% 1.82/0.98  
% 1.82/0.98  fof(f54,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f31])).
% 1.82/0.98  
% 1.82/0.98  fof(f63,plain,(
% 1.82/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f40,plain,(
% 1.82/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f16])).
% 1.82/0.98  
% 1.82/0.98  cnf(c_19,negated_conjecture,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.82/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_813,negated_conjecture,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1087,plain,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_13,plain,
% 1.82/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_24,negated_conjecture,
% 1.82/0.98      ( l1_struct_0(sK0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_278,plain,
% 1.82/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_279,plain,
% 1.82/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_278]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_809,plain,
% 1.82/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_279]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_22,negated_conjecture,
% 1.82/0.98      ( l1_struct_0(sK1) ),
% 1.82/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_273,plain,
% 1.82/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_274,plain,
% 1.82/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_273]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_810,plain,
% 1.82/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_274]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1109,plain,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_1087,c_809,c_810]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_5,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_816,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k2_relset_1(X0_54,X1_54,X0_51) = k2_relat_1(X0_51) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1086,plain,
% 1.82/0.98      ( k2_relset_1(X0_54,X1_54,X0_51) = k2_relat_1(X0_51)
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1304,plain,
% 1.82/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_1109,c_1086]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_18,negated_conjecture,
% 1.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.82/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_814,negated_conjecture,
% 1.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1106,plain,
% 1.82/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_814,c_809,c_810]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1349,plain,
% 1.82/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1304,c_1106]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1401,plain,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1349,c_1109]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_6,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | v1_partfun1(X0,X1)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | v1_xboole_0(X2)
% 1.82/0.98      | ~ v1_funct_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_14,plain,
% 1.82/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.82/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_23,negated_conjecture,
% 1.82/0.98      ( ~ v2_struct_0(sK1) ),
% 1.82/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_260,plain,
% 1.82/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_261,plain,
% 1.82/0.98      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_260]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_36,plain,
% 1.82/0.98      ( v2_struct_0(sK1)
% 1.82/0.98      | ~ l1_struct_0(sK1)
% 1.82/0.98      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.82/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_263,plain,
% 1.82/0.98      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_261,c_23,c_22,c_36]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_285,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | v1_partfun1(X0,X1)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_struct_0(sK1) != X2 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_263]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_286,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.82/0.98      | v1_partfun1(X0,X1)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.82/0.98      | ~ v1_funct_1(X0) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_285]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_3,plain,
% 1.82/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.82/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_9,plain,
% 1.82/0.98      ( ~ v1_partfun1(X0,X1)
% 1.82/0.98      | ~ v4_relat_1(X0,X1)
% 1.82/0.98      | ~ v1_relat_1(X0)
% 1.82/0.98      | k1_relat_1(X0) = X1 ),
% 1.82/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_308,plain,
% 1.82/0.98      ( ~ v1_partfun1(X0,X1)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_relat_1(X0)
% 1.82/0.98      | k1_relat_1(X0) = X1 ),
% 1.82/0.98      inference(resolution,[status(thm)],[c_3,c_9]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_312,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_partfun1(X0,X1)
% 1.82/0.98      | k1_relat_1(X0) = X1 ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_308,c_9,c_3,c_2]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_313,plain,
% 1.82/0.98      ( ~ v1_partfun1(X0,X1)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | k1_relat_1(X0) = X1 ),
% 1.82/0.98      inference(renaming,[status(thm)],[c_312]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_394,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k1_relat_1(X0) = X1 ),
% 1.82/0.98      inference(resolution,[status(thm)],[c_286,c_313]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_808,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0_51,X0_54,k2_struct_0(sK1))
% 1.82/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
% 1.82/0.98      | ~ v1_funct_1(X0_51)
% 1.82/0.98      | k1_relat_1(X0_51) = X0_54 ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_394]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1090,plain,
% 1.82/0.98      ( k1_relat_1(X0_51) = X0_54
% 1.82/0.98      | v1_funct_2(X0_51,X0_54,k2_struct_0(sK1)) != iProver_top
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 1.82/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1664,plain,
% 1.82/0.98      ( k1_relat_1(X0_51) = X0_54
% 1.82/0.98      | v1_funct_2(X0_51,X0_54,k2_relat_1(sK2)) != iProver_top
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_relat_1(sK2)))) != iProver_top
% 1.82/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_1090,c_1349]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1741,plain,
% 1.82/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.82/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
% 1.82/0.98      | v1_funct_1(sK2) != iProver_top ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_1401,c_1664]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_21,negated_conjecture,
% 1.82/0.98      ( v1_funct_1(sK2) ),
% 1.82/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_28,plain,
% 1.82/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_20,negated_conjecture,
% 1.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.82/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_812,negated_conjecture,
% 1.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1088,plain,
% 1.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1103,plain,
% 1.82/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_1088,c_809,c_810]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1402,plain,
% 1.82/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1349,c_1103]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1399,plain,
% 1.82/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1349,c_1304]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_10,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | ~ v2_funct_1(X0)
% 1.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.82/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_17,negated_conjecture,
% 1.82/0.98      ( v2_funct_1(sK2) ),
% 1.82/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_494,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_495,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | ~ v1_funct_1(sK2)
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_494]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_499,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.82/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(global_propositional_subsumption,[status(thm)],[c_495,c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_500,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(renaming,[status(thm)],[c_499]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_804,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0_54,X1_54)
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k2_relset_1(X0_54,X1_54,sK2) != X1_54 ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_500]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1094,plain,
% 1.82/0.98      ( k2_relset_1(X0_54,X1_54,sK2) != X1_54
% 1.82/0.98      | v1_funct_2(sK2,X0_54,X1_54) != iProver_top
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1638,plain,
% 1.82/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_1399,c_1094]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2091,plain,
% 1.82/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_1638,c_1401,c_1402]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_4,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_817,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k1_relset_1(X0_54,X1_54,X0_51) = k1_relat_1(X0_51) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1085,plain,
% 1.82/0.98      ( k1_relset_1(X0_54,X1_54,X0_51) = k1_relat_1(X0_51)
% 1.82/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2097,plain,
% 1.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_2091,c_1085]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1,plain,
% 1.82/0.98      ( ~ v1_relat_1(X0)
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | ~ v2_funct_1(X0)
% 1.82/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_518,plain,
% 1.82/0.98      ( ~ v1_relat_1(X0)
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_519,plain,
% 1.82/0.98      ( ~ v1_relat_1(sK2)
% 1.82/0.98      | ~ v1_funct_1(sK2)
% 1.82/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_518]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_521,plain,
% 1.82/0.98      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,[status(thm)],[c_519,c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_584,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_521]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_585,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_584]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_802,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_585]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1096,plain,
% 1.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1217,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.82/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(instantiation,[status(thm)],[c_802]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1872,plain,
% 1.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_1096,c_19,c_1217]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2099,plain,
% 1.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_2097,c_1872]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_15,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | ~ v2_funct_1(X0)
% 1.82/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.82/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_422,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_423,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | ~ v1_funct_1(sK2)
% 1.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_422]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_427,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(global_propositional_subsumption,[status(thm)],[c_423,c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_428,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 1.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.82/0.98      inference(renaming,[status(thm)],[c_427]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_807,plain,
% 1.82/0.98      ( ~ v1_funct_2(sK2,X0_54,X1_54)
% 1.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k2_relset_1(X0_54,X1_54,sK2) != X1_54
% 1.82/0.98      | k2_tops_2(X0_54,X1_54,sK2) = k2_funct_1(sK2) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_428]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1091,plain,
% 1.82/0.98      ( k2_relset_1(X0_54,X1_54,sK2) != X1_54
% 1.82/0.98      | k2_tops_2(X0_54,X1_54,sK2) = k2_funct_1(sK2)
% 1.82/0.98      | v1_funct_2(sK2,X0_54,X1_54) != iProver_top
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1640,plain,
% 1.82/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 1.82/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_1399,c_1091]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1986,plain,
% 1.82/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_1640,c_1401,c_1402]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_16,negated_conjecture,
% 1.82/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.82/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_815,negated_conjecture,
% 1.82/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1128,plain,
% 1.82/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_815,c_809,c_810]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1403,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1349,c_1128]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1989,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_1986,c_1403]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2197,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.82/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 1.82/0.98      inference(demodulation,[status(thm)],[c_2099,c_1989]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2286,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 1.82/0.98      inference(equality_resolution_simp,[status(thm)],[c_2197]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2096,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_2091,c_1086]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_0,plain,
% 1.82/0.98      ( ~ v1_relat_1(X0)
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | ~ v2_funct_1(X0)
% 1.82/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_532,plain,
% 1.82/0.98      ( ~ v1_relat_1(X0)
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_533,plain,
% 1.82/0.98      ( ~ v1_relat_1(sK2)
% 1.82/0.98      | ~ v1_funct_1(sK2)
% 1.82/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_532]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_535,plain,
% 1.82/0.98      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,[status(thm)],[c_533,c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_572,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.82/0.98      | sK2 != X0 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_535]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_573,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_572]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_803,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_573]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1095,plain,
% 1.82/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1220,plain,
% 1.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.82/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(instantiation,[status(thm)],[c_803]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1868,plain,
% 1.82/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_1095,c_19,c_1220]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2102,plain,
% 1.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_2096,c_1868]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2287,plain,
% 1.82/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 1.82/0.98      inference(light_normalisation,[status(thm)],[c_2286,c_2102]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2290,plain,
% 1.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_1741,c_28,c_1402,c_2287]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2297,plain,
% 1.82/0.98      ( $false ),
% 1.82/0.98      inference(superposition,[status(thm)],[c_1401,c_2290]) ).
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  ------                               Statistics
% 1.82/0.98  
% 1.82/0.98  ------ General
% 1.82/0.98  
% 1.82/0.98  abstr_ref_over_cycles:                  0
% 1.82/0.98  abstr_ref_under_cycles:                 0
% 1.82/0.98  gc_basic_clause_elim:                   0
% 1.82/0.98  forced_gc_time:                         0
% 1.82/0.98  parsing_time:                           0.008
% 1.82/0.98  unif_index_cands_time:                  0.
% 1.82/0.98  unif_index_add_time:                    0.
% 1.82/0.98  orderings_time:                         0.
% 1.82/0.98  out_proof_time:                         0.013
% 1.82/0.98  total_time:                             0.111
% 1.82/0.98  num_of_symbols:                         56
% 1.82/0.98  num_of_terms:                           2026
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing
% 1.82/0.98  
% 1.82/0.98  num_of_splits:                          0
% 1.82/0.98  num_of_split_atoms:                     0
% 1.82/0.98  num_of_reused_defs:                     0
% 1.82/0.98  num_eq_ax_congr_red:                    6
% 1.82/0.98  num_of_sem_filtered_clauses:            1
% 1.82/0.98  num_of_subtypes:                        5
% 1.82/0.98  monotx_restored_types:                  1
% 1.82/0.98  sat_num_of_epr_types:                   0
% 1.82/0.98  sat_num_of_non_cyclic_types:            0
% 1.82/0.98  sat_guarded_non_collapsed_types:        0
% 1.82/0.98  num_pure_diseq_elim:                    0
% 1.82/0.98  simp_replaced_by:                       0
% 1.82/0.98  res_preprocessed:                       107
% 1.82/0.98  prep_upred:                             0
% 1.82/0.98  prep_unflattend:                        20
% 1.82/0.98  smt_new_axioms:                         0
% 1.82/0.98  pred_elim_cands:                        3
% 1.82/0.98  pred_elim:                              7
% 1.82/0.98  pred_elim_cl:                           8
% 1.82/0.98  pred_elim_cycles:                       10
% 1.82/0.98  merged_defs:                            0
% 1.82/0.98  merged_defs_ncl:                        0
% 1.82/0.98  bin_hyper_res:                          0
% 1.82/0.98  prep_cycles:                            4
% 1.82/0.98  pred_elim_time:                         0.009
% 1.82/0.98  splitting_time:                         0.
% 1.82/0.98  sem_filter_time:                        0.
% 1.82/0.98  monotx_time:                            0.
% 1.82/0.98  subtype_inf_time:                       0.001
% 1.82/0.98  
% 1.82/0.98  ------ Problem properties
% 1.82/0.98  
% 1.82/0.98  clauses:                                16
% 1.82/0.98  conjectures:                            5
% 1.82/0.98  epr:                                    1
% 1.82/0.98  horn:                                   16
% 1.82/0.98  ground:                                 7
% 1.82/0.98  unary:                                  6
% 1.82/0.98  binary:                                 5
% 1.82/0.98  lits:                                   37
% 1.82/0.98  lits_eq:                                15
% 1.82/0.98  fd_pure:                                0
% 1.82/0.98  fd_pseudo:                              0
% 1.82/0.98  fd_cond:                                0
% 1.82/0.98  fd_pseudo_cond:                         1
% 1.82/0.98  ac_symbols:                             0
% 1.82/0.98  
% 1.82/0.98  ------ Propositional Solver
% 1.82/0.98  
% 1.82/0.98  prop_solver_calls:                      29
% 1.82/0.98  prop_fast_solver_calls:                 723
% 1.82/0.98  smt_solver_calls:                       0
% 1.82/0.98  smt_fast_solver_calls:                  0
% 1.82/0.98  prop_num_of_clauses:                    778
% 1.82/0.98  prop_preprocess_simplified:             3133
% 1.82/0.98  prop_fo_subsumed:                       21
% 1.82/0.98  prop_solver_time:                       0.
% 1.82/0.98  smt_solver_time:                        0.
% 1.82/0.98  smt_fast_solver_time:                   0.
% 1.82/0.98  prop_fast_solver_time:                  0.
% 1.82/0.98  prop_unsat_core_time:                   0.
% 1.82/0.98  
% 1.82/0.98  ------ QBF
% 1.82/0.98  
% 1.82/0.98  qbf_q_res:                              0
% 1.82/0.98  qbf_num_tautologies:                    0
% 1.82/0.98  qbf_prep_cycles:                        0
% 1.82/0.98  
% 1.82/0.98  ------ BMC1
% 1.82/0.98  
% 1.82/0.98  bmc1_current_bound:                     -1
% 1.82/0.98  bmc1_last_solved_bound:                 -1
% 1.82/0.98  bmc1_unsat_core_size:                   -1
% 1.82/0.98  bmc1_unsat_core_parents_size:           -1
% 1.82/0.98  bmc1_merge_next_fun:                    0
% 1.82/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation
% 1.82/0.98  
% 1.82/0.98  inst_num_of_clauses:                    258
% 1.82/0.98  inst_num_in_passive:                    53
% 1.82/0.98  inst_num_in_active:                     158
% 1.82/0.98  inst_num_in_unprocessed:                47
% 1.82/0.98  inst_num_of_loops:                      170
% 1.82/0.98  inst_num_of_learning_restarts:          0
% 1.82/0.98  inst_num_moves_active_passive:          6
% 1.82/0.98  inst_lit_activity:                      0
% 1.82/0.98  inst_lit_activity_moves:                0
% 1.82/0.98  inst_num_tautologies:                   0
% 1.82/0.98  inst_num_prop_implied:                  0
% 1.82/0.98  inst_num_existing_simplified:           0
% 1.82/0.98  inst_num_eq_res_simplified:             0
% 1.82/0.98  inst_num_child_elim:                    0
% 1.82/0.98  inst_num_of_dismatching_blockings:      13
% 1.82/0.98  inst_num_of_non_proper_insts:           215
% 1.82/0.98  inst_num_of_duplicates:                 0
% 1.82/0.98  inst_inst_num_from_inst_to_res:         0
% 1.82/0.98  inst_dismatching_checking_time:         0.
% 1.82/0.98  
% 1.82/0.98  ------ Resolution
% 1.82/0.98  
% 1.82/0.98  res_num_of_clauses:                     0
% 1.82/0.98  res_num_in_passive:                     0
% 1.82/0.98  res_num_in_active:                      0
% 1.82/0.98  res_num_of_loops:                       111
% 1.82/0.98  res_forward_subset_subsumed:            38
% 1.82/0.99  res_backward_subset_subsumed:           0
% 1.82/0.99  res_forward_subsumed:                   0
% 1.82/0.99  res_backward_subsumed:                  0
% 1.82/0.99  res_forward_subsumption_resolution:     1
% 1.82/0.99  res_backward_subsumption_resolution:    0
% 1.82/0.99  res_clause_to_clause_subsumption:       54
% 1.82/0.99  res_orphan_elimination:                 0
% 1.82/0.99  res_tautology_del:                      31
% 1.82/0.99  res_num_eq_res_simplified:              0
% 1.82/0.99  res_num_sel_changes:                    0
% 1.82/0.99  res_moves_from_active_to_pass:          0
% 1.82/0.99  
% 1.82/0.99  ------ Superposition
% 1.82/0.99  
% 1.82/0.99  sup_time_total:                         0.
% 1.82/0.99  sup_time_generating:                    0.
% 1.82/0.99  sup_time_sim_full:                      0.
% 1.82/0.99  sup_time_sim_immed:                     0.
% 1.82/0.99  
% 1.82/0.99  sup_num_of_clauses:                     25
% 1.82/0.99  sup_num_in_active:                      25
% 1.82/0.99  sup_num_in_passive:                     0
% 1.82/0.99  sup_num_of_loops:                       33
% 1.82/0.99  sup_fw_superposition:                   3
% 1.82/0.99  sup_bw_superposition:                   10
% 1.82/0.99  sup_immediate_simplified:               4
% 1.82/0.99  sup_given_eliminated:                   0
% 1.82/0.99  comparisons_done:                       0
% 1.82/0.99  comparisons_avoided:                    0
% 1.82/0.99  
% 1.82/0.99  ------ Simplifications
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  sim_fw_subset_subsumed:                 2
% 1.82/0.99  sim_bw_subset_subsumed:                 0
% 1.82/0.99  sim_fw_subsumed:                        0
% 1.82/0.99  sim_bw_subsumed:                        0
% 1.82/0.99  sim_fw_subsumption_res:                 0
% 1.82/0.99  sim_bw_subsumption_res:                 0
% 1.82/0.99  sim_tautology_del:                      0
% 1.82/0.99  sim_eq_tautology_del:                   0
% 1.82/0.99  sim_eq_res_simp:                        1
% 1.82/0.99  sim_fw_demodulated:                     0
% 1.82/0.99  sim_bw_demodulated:                     9
% 1.82/0.99  sim_light_normalised:                   8
% 1.82/0.99  sim_joinable_taut:                      0
% 1.82/0.99  sim_joinable_simp:                      0
% 1.82/0.99  sim_ac_normalised:                      0
% 1.82/0.99  sim_smt_subsumption:                    0
% 1.82/0.99  
%------------------------------------------------------------------------------
