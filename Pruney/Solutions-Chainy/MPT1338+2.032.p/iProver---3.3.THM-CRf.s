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
% DateTime   : Thu Dec  3 12:17:06 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  174 (1462 expanded)
%              Number of clauses        :  113 ( 458 expanded)
%              Number of leaves         :   18 ( 418 expanded)
%              Depth                    :   23
%              Number of atoms          :  547 (10264 expanded)
%              Number of equality atoms :  230 (3523 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).

fof(f63,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f65,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_662,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_308,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_309,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_656,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_303,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_304,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_657,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_977,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_662,c_656,c_657])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_402,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_22])).

cnf(c_407,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_655,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_958,plain,
    ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_1374,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_958])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_661,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_955,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_980,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_955,c_656,c_657])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_660,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_956,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_974,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_956,c_656,c_657])).

cnf(c_1439,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1374,c_980,c_974])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_666,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_952,plain,
    ( v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_1443,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_952])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2258,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1443,c_29,c_980,c_974])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_951,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1210,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_980,c_951])).

cnf(c_1517,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1210,c_977])).

cnf(c_2262,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2258,c_1517])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_950,plain,
    ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_2267,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2262,c_950])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_425,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_426,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_428,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_22])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_428])).

cnf(c_477,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_960,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_2126,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_20,c_1088])).

cnf(c_2283,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2267,c_2126])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_663,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1007,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_663,c_656,c_657])).

cnf(c_1442,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1439,c_1007])).

cnf(c_1575,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1517,c_1442])).

cnf(c_2641,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2283,c_1575])).

cnf(c_2765,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_2641])).

cnf(c_2266,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2262,c_951])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_439,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_440,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_22])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_442])).

cnf(c_465,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_654,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_959,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1673,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_20,c_1094])).

cnf(c_2286,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2266,c_1673])).

cnf(c_2766,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2765,c_2286])).

cnf(c_675,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1160,plain,
    ( X0_53 != X1_53
    | k2_struct_0(sK0) != X1_53
    | k2_struct_0(sK0) = X0_53 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1703,plain,
    ( X0_53 != u1_struct_0(sK0)
    | k2_struct_0(sK0) = X0_53
    | k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_1938,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_315,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_8])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_8,c_4,c_3])).

cnf(c_320,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_319])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_10,c_320])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_10,c_3,c_315])).

cnf(c_499,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_652,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_499])).

cnf(c_1290,plain,
    ( ~ v1_funct_2(X0_52,X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1653,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1186,plain,
    ( X0_53 != X1_53
    | X0_53 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1_53 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1300,plain,
    ( X0_53 = u1_struct_0(sK0)
    | X0_53 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1186])).

cnf(c_1433,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = u1_struct_0(sK0)
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_671,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1281,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_1190,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_1099,plain,
    ( u1_struct_0(sK1) != X0_53
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != X0_53 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1189,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_276,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_294,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_24])).

cnf(c_295,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_278,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_297,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_24,c_23,c_278])).

cnf(c_658,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2766,c_1938,c_1653,c_1433,c_1281,c_1190,c_1189,c_656,c_658,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.36/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.98  
% 2.36/0.98  ------  iProver source info
% 2.36/0.98  
% 2.36/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.98  git: non_committed_changes: false
% 2.36/0.98  git: last_make_outside_of_git: false
% 2.36/0.98  
% 2.36/0.98  ------ 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options
% 2.36/0.98  
% 2.36/0.98  --out_options                           all
% 2.36/0.98  --tptp_safe_out                         true
% 2.36/0.98  --problem_path                          ""
% 2.36/0.98  --include_path                          ""
% 2.36/0.98  --clausifier                            res/vclausify_rel
% 2.36/0.98  --clausifier_options                    --mode clausify
% 2.36/0.98  --stdin                                 false
% 2.36/0.98  --stats_out                             all
% 2.36/0.98  
% 2.36/0.98  ------ General Options
% 2.36/0.98  
% 2.36/0.98  --fof                                   false
% 2.36/0.98  --time_out_real                         305.
% 2.36/0.98  --time_out_virtual                      -1.
% 2.36/0.98  --symbol_type_check                     false
% 2.36/0.98  --clausify_out                          false
% 2.36/0.98  --sig_cnt_out                           false
% 2.36/0.98  --trig_cnt_out                          false
% 2.36/0.98  --trig_cnt_out_tolerance                1.
% 2.36/0.98  --trig_cnt_out_sk_spl                   false
% 2.36/0.98  --abstr_cl_out                          false
% 2.36/0.98  
% 2.36/0.98  ------ Global Options
% 2.36/0.98  
% 2.36/0.98  --schedule                              default
% 2.36/0.98  --add_important_lit                     false
% 2.36/0.98  --prop_solver_per_cl                    1000
% 2.36/0.98  --min_unsat_core                        false
% 2.36/0.98  --soft_assumptions                      false
% 2.36/0.98  --soft_lemma_size                       3
% 2.36/0.98  --prop_impl_unit_size                   0
% 2.36/0.98  --prop_impl_unit                        []
% 2.36/0.98  --share_sel_clauses                     true
% 2.36/0.98  --reset_solvers                         false
% 2.36/0.98  --bc_imp_inh                            [conj_cone]
% 2.36/0.98  --conj_cone_tolerance                   3.
% 2.36/0.98  --extra_neg_conj                        none
% 2.36/0.98  --large_theory_mode                     true
% 2.36/0.98  --prolific_symb_bound                   200
% 2.36/0.98  --lt_threshold                          2000
% 2.36/0.98  --clause_weak_htbl                      true
% 2.36/0.98  --gc_record_bc_elim                     false
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing Options
% 2.36/0.98  
% 2.36/0.98  --preprocessing_flag                    true
% 2.36/0.98  --time_out_prep_mult                    0.1
% 2.36/0.98  --splitting_mode                        input
% 2.36/0.98  --splitting_grd                         true
% 2.36/0.98  --splitting_cvd                         false
% 2.36/0.98  --splitting_cvd_svl                     false
% 2.36/0.98  --splitting_nvd                         32
% 2.36/0.98  --sub_typing                            true
% 2.36/0.98  --prep_gs_sim                           true
% 2.36/0.98  --prep_unflatten                        true
% 2.36/0.98  --prep_res_sim                          true
% 2.36/0.98  --prep_upred                            true
% 2.36/0.98  --prep_sem_filter                       exhaustive
% 2.36/0.98  --prep_sem_filter_out                   false
% 2.36/0.98  --pred_elim                             true
% 2.36/0.98  --res_sim_input                         true
% 2.36/0.98  --eq_ax_congr_red                       true
% 2.36/0.98  --pure_diseq_elim                       true
% 2.36/0.98  --brand_transform                       false
% 2.36/0.98  --non_eq_to_eq                          false
% 2.36/0.98  --prep_def_merge                        true
% 2.36/0.98  --prep_def_merge_prop_impl              false
% 2.36/0.98  --prep_def_merge_mbd                    true
% 2.36/0.98  --prep_def_merge_tr_red                 false
% 2.36/0.98  --prep_def_merge_tr_cl                  false
% 2.36/0.98  --smt_preprocessing                     true
% 2.36/0.98  --smt_ac_axioms                         fast
% 2.36/0.98  --preprocessed_out                      false
% 2.36/0.98  --preprocessed_stats                    false
% 2.36/0.98  
% 2.36/0.98  ------ Abstraction refinement Options
% 2.36/0.98  
% 2.36/0.98  --abstr_ref                             []
% 2.36/0.98  --abstr_ref_prep                        false
% 2.36/0.98  --abstr_ref_until_sat                   false
% 2.36/0.98  --abstr_ref_sig_restrict                funpre
% 2.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.98  --abstr_ref_under                       []
% 2.36/0.98  
% 2.36/0.98  ------ SAT Options
% 2.36/0.98  
% 2.36/0.98  --sat_mode                              false
% 2.36/0.98  --sat_fm_restart_options                ""
% 2.36/0.98  --sat_gr_def                            false
% 2.36/0.98  --sat_epr_types                         true
% 2.36/0.98  --sat_non_cyclic_types                  false
% 2.36/0.98  --sat_finite_models                     false
% 2.36/0.98  --sat_fm_lemmas                         false
% 2.36/0.98  --sat_fm_prep                           false
% 2.36/0.98  --sat_fm_uc_incr                        true
% 2.36/0.98  --sat_out_model                         small
% 2.36/0.98  --sat_out_clauses                       false
% 2.36/0.98  
% 2.36/0.98  ------ QBF Options
% 2.36/0.98  
% 2.36/0.98  --qbf_mode                              false
% 2.36/0.98  --qbf_elim_univ                         false
% 2.36/0.98  --qbf_dom_inst                          none
% 2.36/0.98  --qbf_dom_pre_inst                      false
% 2.36/0.98  --qbf_sk_in                             false
% 2.36/0.98  --qbf_pred_elim                         true
% 2.36/0.98  --qbf_split                             512
% 2.36/0.98  
% 2.36/0.98  ------ BMC1 Options
% 2.36/0.98  
% 2.36/0.98  --bmc1_incremental                      false
% 2.36/0.98  --bmc1_axioms                           reachable_all
% 2.36/0.98  --bmc1_min_bound                        0
% 2.36/0.98  --bmc1_max_bound                        -1
% 2.36/0.98  --bmc1_max_bound_default                -1
% 2.36/0.98  --bmc1_symbol_reachability              true
% 2.36/0.98  --bmc1_property_lemmas                  false
% 2.36/0.98  --bmc1_k_induction                      false
% 2.36/0.98  --bmc1_non_equiv_states                 false
% 2.36/0.98  --bmc1_deadlock                         false
% 2.36/0.98  --bmc1_ucm                              false
% 2.36/0.98  --bmc1_add_unsat_core                   none
% 2.36/0.98  --bmc1_unsat_core_children              false
% 2.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.98  --bmc1_out_stat                         full
% 2.36/0.98  --bmc1_ground_init                      false
% 2.36/0.98  --bmc1_pre_inst_next_state              false
% 2.36/0.98  --bmc1_pre_inst_state                   false
% 2.36/0.98  --bmc1_pre_inst_reach_state             false
% 2.36/0.98  --bmc1_out_unsat_core                   false
% 2.36/0.98  --bmc1_aig_witness_out                  false
% 2.36/0.98  --bmc1_verbose                          false
% 2.36/0.98  --bmc1_dump_clauses_tptp                false
% 2.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.98  --bmc1_dump_file                        -
% 2.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.98  --bmc1_ucm_extend_mode                  1
% 2.36/0.98  --bmc1_ucm_init_mode                    2
% 2.36/0.98  --bmc1_ucm_cone_mode                    none
% 2.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.98  --bmc1_ucm_relax_model                  4
% 2.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.98  --bmc1_ucm_layered_model                none
% 2.36/0.98  --bmc1_ucm_max_lemma_size               10
% 2.36/0.98  
% 2.36/0.98  ------ AIG Options
% 2.36/0.98  
% 2.36/0.98  --aig_mode                              false
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation Options
% 2.36/0.98  
% 2.36/0.98  --instantiation_flag                    true
% 2.36/0.98  --inst_sos_flag                         false
% 2.36/0.98  --inst_sos_phase                        true
% 2.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel_side                     num_symb
% 2.36/0.98  --inst_solver_per_active                1400
% 2.36/0.98  --inst_solver_calls_frac                1.
% 2.36/0.98  --inst_passive_queue_type               priority_queues
% 2.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.98  --inst_passive_queues_freq              [25;2]
% 2.36/0.98  --inst_dismatching                      true
% 2.36/0.98  --inst_eager_unprocessed_to_passive     true
% 2.36/0.98  --inst_prop_sim_given                   true
% 2.36/0.98  --inst_prop_sim_new                     false
% 2.36/0.98  --inst_subs_new                         false
% 2.36/0.98  --inst_eq_res_simp                      false
% 2.36/0.98  --inst_subs_given                       false
% 2.36/0.98  --inst_orphan_elimination               true
% 2.36/0.98  --inst_learning_loop_flag               true
% 2.36/0.98  --inst_learning_start                   3000
% 2.36/0.98  --inst_learning_factor                  2
% 2.36/0.98  --inst_start_prop_sim_after_learn       3
% 2.36/0.98  --inst_sel_renew                        solver
% 2.36/0.98  --inst_lit_activity_flag                true
% 2.36/0.98  --inst_restr_to_given                   false
% 2.36/0.98  --inst_activity_threshold               500
% 2.36/0.98  --inst_out_proof                        true
% 2.36/0.98  
% 2.36/0.98  ------ Resolution Options
% 2.36/0.98  
% 2.36/0.98  --resolution_flag                       true
% 2.36/0.98  --res_lit_sel                           adaptive
% 2.36/0.98  --res_lit_sel_side                      none
% 2.36/0.98  --res_ordering                          kbo
% 2.36/0.98  --res_to_prop_solver                    active
% 2.36/0.98  --res_prop_simpl_new                    false
% 2.36/0.98  --res_prop_simpl_given                  true
% 2.36/0.98  --res_passive_queue_type                priority_queues
% 2.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.98  --res_passive_queues_freq               [15;5]
% 2.36/0.98  --res_forward_subs                      full
% 2.36/0.98  --res_backward_subs                     full
% 2.36/0.98  --res_forward_subs_resolution           true
% 2.36/0.98  --res_backward_subs_resolution          true
% 2.36/0.98  --res_orphan_elimination                true
% 2.36/0.98  --res_time_limit                        2.
% 2.36/0.98  --res_out_proof                         true
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Options
% 2.36/0.98  
% 2.36/0.98  --superposition_flag                    true
% 2.36/0.98  --sup_passive_queue_type                priority_queues
% 2.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.98  --demod_completeness_check              fast
% 2.36/0.98  --demod_use_ground                      true
% 2.36/0.98  --sup_to_prop_solver                    passive
% 2.36/0.98  --sup_prop_simpl_new                    true
% 2.36/0.98  --sup_prop_simpl_given                  true
% 2.36/0.98  --sup_fun_splitting                     false
% 2.36/0.98  --sup_smt_interval                      50000
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Simplification Setup
% 2.36/0.98  
% 2.36/0.98  --sup_indices_passive                   []
% 2.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_full_bw                           [BwDemod]
% 2.36/0.98  --sup_immed_triv                        [TrivRules]
% 2.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_immed_bw_main                     []
% 2.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  
% 2.36/0.98  ------ Combination Options
% 2.36/0.98  
% 2.36/0.98  --comb_res_mult                         3
% 2.36/0.98  --comb_sup_mult                         2
% 2.36/0.98  --comb_inst_mult                        10
% 2.36/0.98  
% 2.36/0.98  ------ Debug Options
% 2.36/0.98  
% 2.36/0.98  --dbg_backtrace                         false
% 2.36/0.98  --dbg_dump_prop_clauses                 false
% 2.36/0.98  --dbg_dump_prop_clauses_file            -
% 2.36/0.98  --dbg_out_stat                          false
% 2.36/0.98  ------ Parsing...
% 2.36/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.98  ------ Proving...
% 2.36/0.98  ------ Problem Properties 
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  clauses                                 18
% 2.36/0.98  conjectures                             5
% 2.36/0.98  EPR                                     1
% 2.36/0.98  Horn                                    17
% 2.36/0.98  unary                                   7
% 2.36/0.98  binary                                  5
% 2.36/0.98  lits                                    43
% 2.36/0.98  lits eq                                 15
% 2.36/0.98  fd_pure                                 0
% 2.36/0.98  fd_pseudo                               0
% 2.36/0.98  fd_cond                                 0
% 2.36/0.98  fd_pseudo_cond                          1
% 2.36/0.98  AC symbols                              0
% 2.36/0.98  
% 2.36/0.98  ------ Schedule dynamic 5 is on 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  ------ 
% 2.36/0.98  Current options:
% 2.36/0.98  ------ 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options
% 2.36/0.98  
% 2.36/0.98  --out_options                           all
% 2.36/0.98  --tptp_safe_out                         true
% 2.36/0.98  --problem_path                          ""
% 2.36/0.98  --include_path                          ""
% 2.36/0.98  --clausifier                            res/vclausify_rel
% 2.36/0.98  --clausifier_options                    --mode clausify
% 2.36/0.98  --stdin                                 false
% 2.36/0.98  --stats_out                             all
% 2.36/0.98  
% 2.36/0.98  ------ General Options
% 2.36/0.98  
% 2.36/0.98  --fof                                   false
% 2.36/0.98  --time_out_real                         305.
% 2.36/0.98  --time_out_virtual                      -1.
% 2.36/0.98  --symbol_type_check                     false
% 2.36/0.98  --clausify_out                          false
% 2.36/0.98  --sig_cnt_out                           false
% 2.36/0.98  --trig_cnt_out                          false
% 2.36/0.98  --trig_cnt_out_tolerance                1.
% 2.36/0.98  --trig_cnt_out_sk_spl                   false
% 2.36/0.98  --abstr_cl_out                          false
% 2.36/0.98  
% 2.36/0.98  ------ Global Options
% 2.36/0.98  
% 2.36/0.98  --schedule                              default
% 2.36/0.98  --add_important_lit                     false
% 2.36/0.98  --prop_solver_per_cl                    1000
% 2.36/0.98  --min_unsat_core                        false
% 2.36/0.98  --soft_assumptions                      false
% 2.36/0.98  --soft_lemma_size                       3
% 2.36/0.98  --prop_impl_unit_size                   0
% 2.36/0.98  --prop_impl_unit                        []
% 2.36/0.98  --share_sel_clauses                     true
% 2.36/0.98  --reset_solvers                         false
% 2.36/0.98  --bc_imp_inh                            [conj_cone]
% 2.36/0.98  --conj_cone_tolerance                   3.
% 2.36/0.98  --extra_neg_conj                        none
% 2.36/0.98  --large_theory_mode                     true
% 2.36/0.98  --prolific_symb_bound                   200
% 2.36/0.98  --lt_threshold                          2000
% 2.36/0.98  --clause_weak_htbl                      true
% 2.36/0.98  --gc_record_bc_elim                     false
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing Options
% 2.36/0.98  
% 2.36/0.98  --preprocessing_flag                    true
% 2.36/0.98  --time_out_prep_mult                    0.1
% 2.36/0.98  --splitting_mode                        input
% 2.36/0.98  --splitting_grd                         true
% 2.36/0.98  --splitting_cvd                         false
% 2.36/0.98  --splitting_cvd_svl                     false
% 2.36/0.98  --splitting_nvd                         32
% 2.36/0.98  --sub_typing                            true
% 2.36/0.98  --prep_gs_sim                           true
% 2.36/0.98  --prep_unflatten                        true
% 2.36/0.98  --prep_res_sim                          true
% 2.36/0.98  --prep_upred                            true
% 2.36/0.98  --prep_sem_filter                       exhaustive
% 2.36/0.98  --prep_sem_filter_out                   false
% 2.36/0.98  --pred_elim                             true
% 2.36/0.98  --res_sim_input                         true
% 2.36/0.98  --eq_ax_congr_red                       true
% 2.36/0.98  --pure_diseq_elim                       true
% 2.36/0.98  --brand_transform                       false
% 2.36/0.98  --non_eq_to_eq                          false
% 2.36/0.98  --prep_def_merge                        true
% 2.36/0.98  --prep_def_merge_prop_impl              false
% 2.36/0.98  --prep_def_merge_mbd                    true
% 2.36/0.98  --prep_def_merge_tr_red                 false
% 2.36/0.98  --prep_def_merge_tr_cl                  false
% 2.36/0.98  --smt_preprocessing                     true
% 2.36/0.98  --smt_ac_axioms                         fast
% 2.36/0.98  --preprocessed_out                      false
% 2.36/0.98  --preprocessed_stats                    false
% 2.36/0.98  
% 2.36/0.98  ------ Abstraction refinement Options
% 2.36/0.98  
% 2.36/0.98  --abstr_ref                             []
% 2.36/0.98  --abstr_ref_prep                        false
% 2.36/0.98  --abstr_ref_until_sat                   false
% 2.36/0.98  --abstr_ref_sig_restrict                funpre
% 2.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.98  --abstr_ref_under                       []
% 2.36/0.98  
% 2.36/0.98  ------ SAT Options
% 2.36/0.98  
% 2.36/0.98  --sat_mode                              false
% 2.36/0.98  --sat_fm_restart_options                ""
% 2.36/0.98  --sat_gr_def                            false
% 2.36/0.98  --sat_epr_types                         true
% 2.36/0.98  --sat_non_cyclic_types                  false
% 2.36/0.98  --sat_finite_models                     false
% 2.36/0.98  --sat_fm_lemmas                         false
% 2.36/0.98  --sat_fm_prep                           false
% 2.36/0.98  --sat_fm_uc_incr                        true
% 2.36/0.98  --sat_out_model                         small
% 2.36/0.98  --sat_out_clauses                       false
% 2.36/0.98  
% 2.36/0.98  ------ QBF Options
% 2.36/0.98  
% 2.36/0.98  --qbf_mode                              false
% 2.36/0.98  --qbf_elim_univ                         false
% 2.36/0.98  --qbf_dom_inst                          none
% 2.36/0.98  --qbf_dom_pre_inst                      false
% 2.36/0.98  --qbf_sk_in                             false
% 2.36/0.98  --qbf_pred_elim                         true
% 2.36/0.98  --qbf_split                             512
% 2.36/0.98  
% 2.36/0.98  ------ BMC1 Options
% 2.36/0.98  
% 2.36/0.98  --bmc1_incremental                      false
% 2.36/0.98  --bmc1_axioms                           reachable_all
% 2.36/0.98  --bmc1_min_bound                        0
% 2.36/0.98  --bmc1_max_bound                        -1
% 2.36/0.98  --bmc1_max_bound_default                -1
% 2.36/0.98  --bmc1_symbol_reachability              true
% 2.36/0.98  --bmc1_property_lemmas                  false
% 2.36/0.98  --bmc1_k_induction                      false
% 2.36/0.98  --bmc1_non_equiv_states                 false
% 2.36/0.98  --bmc1_deadlock                         false
% 2.36/0.98  --bmc1_ucm                              false
% 2.36/0.98  --bmc1_add_unsat_core                   none
% 2.36/0.98  --bmc1_unsat_core_children              false
% 2.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.98  --bmc1_out_stat                         full
% 2.36/0.98  --bmc1_ground_init                      false
% 2.36/0.98  --bmc1_pre_inst_next_state              false
% 2.36/0.98  --bmc1_pre_inst_state                   false
% 2.36/0.98  --bmc1_pre_inst_reach_state             false
% 2.36/0.98  --bmc1_out_unsat_core                   false
% 2.36/0.98  --bmc1_aig_witness_out                  false
% 2.36/0.98  --bmc1_verbose                          false
% 2.36/0.98  --bmc1_dump_clauses_tptp                false
% 2.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.98  --bmc1_dump_file                        -
% 2.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.98  --bmc1_ucm_extend_mode                  1
% 2.36/0.98  --bmc1_ucm_init_mode                    2
% 2.36/0.98  --bmc1_ucm_cone_mode                    none
% 2.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.98  --bmc1_ucm_relax_model                  4
% 2.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.98  --bmc1_ucm_layered_model                none
% 2.36/0.98  --bmc1_ucm_max_lemma_size               10
% 2.36/0.98  
% 2.36/0.98  ------ AIG Options
% 2.36/0.98  
% 2.36/0.98  --aig_mode                              false
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation Options
% 2.36/0.98  
% 2.36/0.98  --instantiation_flag                    true
% 2.36/0.98  --inst_sos_flag                         false
% 2.36/0.98  --inst_sos_phase                        true
% 2.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel_side                     none
% 2.36/0.98  --inst_solver_per_active                1400
% 2.36/0.98  --inst_solver_calls_frac                1.
% 2.36/0.98  --inst_passive_queue_type               priority_queues
% 2.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.98  --inst_passive_queues_freq              [25;2]
% 2.36/0.98  --inst_dismatching                      true
% 2.36/0.98  --inst_eager_unprocessed_to_passive     true
% 2.36/0.98  --inst_prop_sim_given                   true
% 2.36/0.98  --inst_prop_sim_new                     false
% 2.36/0.98  --inst_subs_new                         false
% 2.36/0.98  --inst_eq_res_simp                      false
% 2.36/0.98  --inst_subs_given                       false
% 2.36/0.98  --inst_orphan_elimination               true
% 2.36/0.98  --inst_learning_loop_flag               true
% 2.36/0.98  --inst_learning_start                   3000
% 2.36/0.98  --inst_learning_factor                  2
% 2.36/0.98  --inst_start_prop_sim_after_learn       3
% 2.36/0.98  --inst_sel_renew                        solver
% 2.36/0.98  --inst_lit_activity_flag                true
% 2.36/0.98  --inst_restr_to_given                   false
% 2.36/0.98  --inst_activity_threshold               500
% 2.36/0.98  --inst_out_proof                        true
% 2.36/0.98  
% 2.36/0.98  ------ Resolution Options
% 2.36/0.98  
% 2.36/0.98  --resolution_flag                       false
% 2.36/0.98  --res_lit_sel                           adaptive
% 2.36/0.98  --res_lit_sel_side                      none
% 2.36/0.98  --res_ordering                          kbo
% 2.36/0.98  --res_to_prop_solver                    active
% 2.36/0.98  --res_prop_simpl_new                    false
% 2.36/0.98  --res_prop_simpl_given                  true
% 2.36/0.98  --res_passive_queue_type                priority_queues
% 2.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.98  --res_passive_queues_freq               [15;5]
% 2.36/0.98  --res_forward_subs                      full
% 2.36/0.98  --res_backward_subs                     full
% 2.36/0.98  --res_forward_subs_resolution           true
% 2.36/0.98  --res_backward_subs_resolution          true
% 2.36/0.98  --res_orphan_elimination                true
% 2.36/0.98  --res_time_limit                        2.
% 2.36/0.98  --res_out_proof                         true
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Options
% 2.36/0.98  
% 2.36/0.98  --superposition_flag                    true
% 2.36/0.98  --sup_passive_queue_type                priority_queues
% 2.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.98  --demod_completeness_check              fast
% 2.36/0.98  --demod_use_ground                      true
% 2.36/0.98  --sup_to_prop_solver                    passive
% 2.36/0.98  --sup_prop_simpl_new                    true
% 2.36/0.98  --sup_prop_simpl_given                  true
% 2.36/0.98  --sup_fun_splitting                     false
% 2.36/0.98  --sup_smt_interval                      50000
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Simplification Setup
% 2.36/0.98  
% 2.36/0.98  --sup_indices_passive                   []
% 2.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_full_bw                           [BwDemod]
% 2.36/0.98  --sup_immed_triv                        [TrivRules]
% 2.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_immed_bw_main                     []
% 2.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  
% 2.36/0.98  ------ Combination Options
% 2.36/0.98  
% 2.36/0.98  --comb_res_mult                         3
% 2.36/0.98  --comb_sup_mult                         2
% 2.36/0.98  --comb_inst_mult                        10
% 2.36/0.98  
% 2.36/0.98  ------ Debug Options
% 2.36/0.98  
% 2.36/0.98  --dbg_backtrace                         false
% 2.36/0.98  --dbg_dump_prop_clauses                 false
% 2.36/0.98  --dbg_dump_prop_clauses_file            -
% 2.36/0.98  --dbg_out_stat                          false
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  ------ Proving...
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  % SZS status Theorem for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  fof(f13,conjecture,(
% 2.36/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f14,negated_conjecture,(
% 2.36/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.36/0.98    inference(negated_conjecture,[],[f13])).
% 2.36/0.98  
% 2.36/0.98  fof(f33,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.36/0.98    inference(ennf_transformation,[],[f14])).
% 2.36/0.98  
% 2.36/0.98  fof(f34,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.36/0.98    inference(flattening,[],[f33])).
% 2.36/0.98  
% 2.36/0.98  fof(f38,plain,(
% 2.36/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f37,plain,(
% 2.36/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f36,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f39,plain,(
% 2.36/0.98    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.36/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).
% 2.36/0.98  
% 2.36/0.98  fof(f63,plain,(
% 2.36/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f9,axiom,(
% 2.36/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f26,plain,(
% 2.36/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.36/0.98    inference(ennf_transformation,[],[f9])).
% 2.36/0.98  
% 2.36/0.98  fof(f51,plain,(
% 2.36/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f26])).
% 2.36/0.98  
% 2.36/0.98  fof(f57,plain,(
% 2.36/0.98    l1_struct_0(sK0)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f59,plain,(
% 2.36/0.98    l1_struct_0(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f11,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f29,plain,(
% 2.36/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.36/0.98    inference(ennf_transformation,[],[f11])).
% 2.36/0.98  
% 2.36/0.98  fof(f30,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.36/0.98    inference(flattening,[],[f29])).
% 2.36/0.98  
% 2.36/0.98  fof(f53,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f30])).
% 2.36/0.98  
% 2.36/0.98  fof(f64,plain,(
% 2.36/0.98    v2_funct_1(sK2)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f60,plain,(
% 2.36/0.98    v1_funct_1(sK2)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f62,plain,(
% 2.36/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f61,plain,(
% 2.36/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f12,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f31,plain,(
% 2.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.36/0.98    inference(ennf_transformation,[],[f12])).
% 2.36/0.98  
% 2.36/0.98  fof(f32,plain,(
% 2.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.36/0.98    inference(flattening,[],[f31])).
% 2.36/0.98  
% 2.36/0.98  fof(f56,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f32])).
% 2.36/0.98  
% 2.36/0.98  fof(f6,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f21,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.98    inference(ennf_transformation,[],[f6])).
% 2.36/0.98  
% 2.36/0.98  fof(f46,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.98    inference(cnf_transformation,[],[f21])).
% 2.36/0.98  
% 2.36/0.98  fof(f5,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f20,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.98    inference(ennf_transformation,[],[f5])).
% 2.36/0.98  
% 2.36/0.98  fof(f45,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.98    inference(cnf_transformation,[],[f20])).
% 2.36/0.98  
% 2.36/0.98  fof(f3,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f18,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.98    inference(ennf_transformation,[],[f3])).
% 2.36/0.98  
% 2.36/0.98  fof(f43,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.98    inference(cnf_transformation,[],[f18])).
% 2.36/0.98  
% 2.36/0.98  fof(f2,axiom,(
% 2.36/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f16,plain,(
% 2.36/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.36/0.98    inference(ennf_transformation,[],[f2])).
% 2.36/0.98  
% 2.36/0.98  fof(f17,plain,(
% 2.36/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.36/0.98    inference(flattening,[],[f16])).
% 2.36/0.98  
% 2.36/0.98  fof(f41,plain,(
% 2.36/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f17])).
% 2.36/0.98  
% 2.36/0.98  fof(f65,plain,(
% 2.36/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  fof(f42,plain,(
% 2.36/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f17])).
% 2.36/0.98  
% 2.36/0.98  fof(f8,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f24,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.36/0.98    inference(ennf_transformation,[],[f8])).
% 2.36/0.98  
% 2.36/0.98  fof(f25,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.36/0.98    inference(flattening,[],[f24])).
% 2.36/0.98  
% 2.36/0.98  fof(f49,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f25])).
% 2.36/0.98  
% 2.36/0.98  fof(f4,axiom,(
% 2.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f15,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.36/0.98    inference(pure_predicate_removal,[],[f4])).
% 2.36/0.98  
% 2.36/0.98  fof(f19,plain,(
% 2.36/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.98    inference(ennf_transformation,[],[f15])).
% 2.36/0.98  
% 2.36/0.98  fof(f44,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.98    inference(cnf_transformation,[],[f19])).
% 2.36/0.98  
% 2.36/0.98  fof(f7,axiom,(
% 2.36/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f22,plain,(
% 2.36/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.36/0.98    inference(ennf_transformation,[],[f7])).
% 2.36/0.98  
% 2.36/0.98  fof(f23,plain,(
% 2.36/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/0.98    inference(flattening,[],[f22])).
% 2.36/0.98  
% 2.36/0.98  fof(f35,plain,(
% 2.36/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/0.98    inference(nnf_transformation,[],[f23])).
% 2.36/0.98  
% 2.36/0.98  fof(f47,plain,(
% 2.36/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f35])).
% 2.36/0.98  
% 2.36/0.98  fof(f1,axiom,(
% 2.36/0.98    v1_xboole_0(k1_xboole_0)),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f40,plain,(
% 2.36/0.98    v1_xboole_0(k1_xboole_0)),
% 2.36/0.98    inference(cnf_transformation,[],[f1])).
% 2.36/0.98  
% 2.36/0.98  fof(f10,axiom,(
% 2.36/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f27,plain,(
% 2.36/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.36/0.98    inference(ennf_transformation,[],[f10])).
% 2.36/0.98  
% 2.36/0.98  fof(f28,plain,(
% 2.36/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.36/0.98    inference(flattening,[],[f27])).
% 2.36/0.98  
% 2.36/0.98  fof(f52,plain,(
% 2.36/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f28])).
% 2.36/0.98  
% 2.36/0.98  fof(f58,plain,(
% 2.36/0.98    ~v2_struct_0(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f39])).
% 2.36/0.98  
% 2.36/0.98  cnf(c_19,negated_conjecture,
% 2.36/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_662,negated_conjecture,
% 2.36/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_11,plain,
% 2.36/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_25,negated_conjecture,
% 2.36/0.98      ( l1_struct_0(sK0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_308,plain,
% 2.36/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_309,plain,
% 2.36/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_308]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_656,plain,
% 2.36/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_309]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_23,negated_conjecture,
% 2.36/0.98      ( l1_struct_0(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_303,plain,
% 2.36/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_304,plain,
% 2.36/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_657,plain,
% 2.36/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_304]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_977,plain,
% 2.36/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_662,c_656,c_657]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_13,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | ~ v2_funct_1(X0)
% 2.36/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.36/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.36/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_18,negated_conjecture,
% 2.36/0.98      ( v2_funct_1(sK2) ),
% 2.36/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_401,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.36/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.36/0.98      | sK2 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_402,plain,
% 2.36/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.36/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.36/0.98      | ~ v1_funct_1(sK2)
% 2.36/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.36/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_401]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_22,negated_conjecture,
% 2.36/0.98      ( v1_funct_1(sK2) ),
% 2.36/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_406,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.36/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.36/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.36/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_402,c_22]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_407,plain,
% 2.36/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.36/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.36/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.36/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.36/0.98      inference(renaming,[status(thm)],[c_406]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_655,plain,
% 2.36/0.98      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 2.36/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.36/0.98      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_407]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_958,plain,
% 2.36/0.98      ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.36/0.98      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
% 2.36/0.98      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 2.36/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1374,plain,
% 2.36/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.36/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.36/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.36/0.98      inference(superposition,[status(thm)],[c_977,c_958]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_20,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.36/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_661,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_955,plain,
% 2.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_980,plain,
% 2.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_955,c_656,c_657]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_21,negated_conjecture,
% 2.36/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_660,negated_conjecture,
% 2.36/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_956,plain,
% 2.36/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_974,plain,
% 2.36/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_956,c_656,c_657]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1439,plain,
% 2.36/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_1374,c_980,c_974]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_14,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.36/0.98      | ~ v1_funct_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_666,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.36/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.36/0.98      | ~ v1_funct_1(X0_52) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_952,plain,
% 2.36/0.98      ( v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.36/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.36/0.98      | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.36/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1443,plain,
% 2.36/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.36/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.36/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.36/0.98      inference(superposition,[status(thm)],[c_1439,c_952]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_29,plain,
% 2.36/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2258,plain,
% 2.36/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_1443,c_29,c_980,c_974]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_6,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_667,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_951,plain,
% 2.36/0.98      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.36/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1210,plain,
% 2.36/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(superposition,[status(thm)],[c_980,c_951]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1517,plain,
% 2.36/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(demodulation,[status(thm)],[c_1210,c_977]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2262,plain,
% 2.36/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2258,c_1517]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_5,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_668,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_950,plain,
% 2.36/0.98      ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
% 2.36/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2267,plain,
% 2.36/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.36/0.98      inference(superposition,[status(thm)],[c_2262,c_950]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | v1_relat_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2,plain,
% 2.36/0.98      ( ~ v1_relat_1(X0)
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | ~ v2_funct_1(X0)
% 2.36/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_425,plain,
% 2.36/0.98      ( ~ v1_relat_1(X0)
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.36/0.98      | sK2 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_426,plain,
% 2.36/0.98      ( ~ v1_relat_1(sK2)
% 2.36/0.98      | ~ v1_funct_1(sK2)
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_425]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_428,plain,
% 2.36/0.98      ( ~ v1_relat_1(sK2)
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_426,c_22]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_476,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.36/0.98      | sK2 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_428]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_477,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_476]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_653,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_477]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_960,plain,
% 2.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.36/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1088,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_653]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2126,plain,
% 2.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_960,c_20,c_1088]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2283,plain,
% 2.36/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2267,c_2126]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_17,negated_conjecture,
% 2.36/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_663,negated_conjecture,
% 2.36/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1007,plain,
% 2.36/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_663,c_656,c_657]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1442,plain,
% 2.36/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.36/0.98      inference(demodulation,[status(thm)],[c_1439,c_1007]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1575,plain,
% 2.36/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.36/0.98      inference(demodulation,[status(thm)],[c_1517,c_1442]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2641,plain,
% 2.36/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.36/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.36/0.98      inference(demodulation,[status(thm)],[c_2283,c_1575]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2765,plain,
% 2.36/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.36/0.98      inference(equality_resolution_simp,[status(thm)],[c_2641]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2266,plain,
% 2.36/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.36/0.98      inference(superposition,[status(thm)],[c_2262,c_951]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1,plain,
% 2.36/0.98      ( ~ v1_relat_1(X0)
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | ~ v2_funct_1(X0)
% 2.36/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_439,plain,
% 2.36/0.98      ( ~ v1_relat_1(X0)
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.36/0.98      | sK2 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_440,plain,
% 2.36/0.98      ( ~ v1_relat_1(sK2)
% 2.36/0.98      | ~ v1_funct_1(sK2)
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_439]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_442,plain,
% 2.36/0.98      ( ~ v1_relat_1(sK2)
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_440,c_22]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_464,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.36/0.98      | sK2 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_442]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_465,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_464]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_654,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_465]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_959,plain,
% 2.36/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.36/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1094,plain,
% 2.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_654]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1673,plain,
% 2.36/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_959,c_20,c_1094]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2286,plain,
% 2.36/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2266,c_1673]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2766,plain,
% 2.36/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2765,c_2286]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_675,plain,
% 2.36/0.98      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 2.36/0.98      theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1160,plain,
% 2.36/0.98      ( X0_53 != X1_53
% 2.36/0.98      | k2_struct_0(sK0) != X1_53
% 2.36/0.98      | k2_struct_0(sK0) = X0_53 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_675]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1703,plain,
% 2.36/0.98      ( X0_53 != u1_struct_0(sK0)
% 2.36/0.98      | k2_struct_0(sK0) = X0_53
% 2.36/0.98      | k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1160]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1938,plain,
% 2.36/0.98      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 2.36/0.98      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.36/0.98      | k1_relat_1(sK2) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1703]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_10,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | v1_partfun1(X0,X1)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k1_xboole_0 = X2 ),
% 2.36/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4,plain,
% 2.36/0.98      ( v4_relat_1(X0,X1)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.36/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_8,plain,
% 2.36/0.98      ( ~ v1_partfun1(X0,X1)
% 2.36/0.98      | ~ v4_relat_1(X0,X1)
% 2.36/0.98      | ~ v1_relat_1(X0)
% 2.36/0.98      | k1_relat_1(X0) = X1 ),
% 2.36/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_315,plain,
% 2.36/0.98      ( ~ v1_partfun1(X0,X1)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_relat_1(X0)
% 2.36/0.98      | k1_relat_1(X0) = X1 ),
% 2.36/0.98      inference(resolution,[status(thm)],[c_4,c_8]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_319,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_partfun1(X0,X1)
% 2.36/0.98      | k1_relat_1(X0) = X1 ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_315,c_8,c_4,c_3]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_320,plain,
% 2.36/0.98      ( ~ v1_partfun1(X0,X1)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | k1_relat_1(X0) = X1 ),
% 2.36/0.98      inference(renaming,[status(thm)],[c_319]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_494,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k1_relat_1(X0) = X1
% 2.36/0.98      | k1_xboole_0 = X2 ),
% 2.36/0.98      inference(resolution,[status(thm)],[c_10,c_320]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_498,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k1_relat_1(X0) = X1
% 2.36/0.98      | k1_xboole_0 = X2 ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_494,c_10,c_3,c_315]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_499,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.98      | ~ v1_funct_1(X0)
% 2.36/0.98      | k1_relat_1(X0) = X1
% 2.36/0.98      | k1_xboole_0 = X2 ),
% 2.36/0.98      inference(renaming,[status(thm)],[c_498]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_652,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.36/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.36/0.98      | ~ v1_funct_1(X0_52)
% 2.36/0.98      | k1_relat_1(X0_52) = X0_53
% 2.36/0.98      | k1_xboole_0 = X1_53 ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_499]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1290,plain,
% 2.36/0.98      ( ~ v1_funct_2(X0_52,X0_53,u1_struct_0(sK1))
% 2.36/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1))))
% 2.36/0.98      | ~ v1_funct_1(X0_52)
% 2.36/0.98      | k1_relat_1(X0_52) = X0_53
% 2.36/0.98      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_652]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1653,plain,
% 2.36/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.36/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.36/0.98      | ~ v1_funct_1(sK2)
% 2.36/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.36/0.98      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1290]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1186,plain,
% 2.36/0.98      ( X0_53 != X1_53
% 2.36/0.98      | X0_53 = u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK0) != X1_53 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_675]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1300,plain,
% 2.36/0.98      ( X0_53 = u1_struct_0(sK0)
% 2.36/0.98      | X0_53 != k2_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1186]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1433,plain,
% 2.36/0.98      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.36/0.98      | k2_struct_0(sK0) = u1_struct_0(sK0)
% 2.36/0.98      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_671,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1281,plain,
% 2.36/0.98      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_671]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1190,plain,
% 2.36/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_671]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1099,plain,
% 2.36/0.98      ( u1_struct_0(sK1) != X0_53
% 2.36/0.98      | u1_struct_0(sK1) = k1_xboole_0
% 2.36/0.98      | k1_xboole_0 != X0_53 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_675]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1189,plain,
% 2.36/0.98      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.36/0.98      | u1_struct_0(sK1) = k1_xboole_0
% 2.36/0.98      | k1_xboole_0 != u1_struct_0(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1099]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_0,plain,
% 2.36/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_12,plain,
% 2.36/0.98      ( v2_struct_0(X0)
% 2.36/0.98      | ~ l1_struct_0(X0)
% 2.36/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_276,plain,
% 2.36/0.98      ( v2_struct_0(X0)
% 2.36/0.98      | ~ l1_struct_0(X0)
% 2.36/0.98      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_24,negated_conjecture,
% 2.36/0.98      ( ~ v2_struct_0(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_294,plain,
% 2.36/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_276,c_24]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_295,plain,
% 2.36/0.98      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_294]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_278,plain,
% 2.36/0.98      ( v2_struct_0(sK1)
% 2.36/0.98      | ~ l1_struct_0(sK1)
% 2.36/0.98      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_276]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_297,plain,
% 2.36/0.98      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_295,c_24,c_23,c_278]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_658,plain,
% 2.36/0.98      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_297]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(contradiction,plain,
% 2.36/0.98      ( $false ),
% 2.36/0.98      inference(minisat,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_2766,c_1938,c_1653,c_1433,c_1281,c_1190,c_1189,c_656,
% 2.36/0.98                 c_658,c_20,c_21,c_22]) ).
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  ------                               Statistics
% 2.36/0.98  
% 2.36/0.98  ------ General
% 2.36/0.98  
% 2.36/0.98  abstr_ref_over_cycles:                  0
% 2.36/0.98  abstr_ref_under_cycles:                 0
% 2.36/0.98  gc_basic_clause_elim:                   0
% 2.36/0.98  forced_gc_time:                         0
% 2.36/0.98  parsing_time:                           0.018
% 2.36/0.98  unif_index_cands_time:                  0.
% 2.36/0.98  unif_index_add_time:                    0.
% 2.36/0.98  orderings_time:                         0.
% 2.36/0.98  out_proof_time:                         0.01
% 2.36/0.98  total_time:                             0.135
% 2.36/0.98  num_of_symbols:                         57
% 2.36/0.98  num_of_terms:                           2488
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing
% 2.36/0.98  
% 2.36/0.98  num_of_splits:                          0
% 2.36/0.98  num_of_split_atoms:                     0
% 2.36/0.98  num_of_reused_defs:                     0
% 2.36/0.98  num_eq_ax_congr_red:                    6
% 2.36/0.98  num_of_sem_filtered_clauses:            1
% 2.36/0.98  num_of_subtypes:                        5
% 2.36/0.98  monotx_restored_types:                  1
% 2.36/0.98  sat_num_of_epr_types:                   0
% 2.36/0.98  sat_num_of_non_cyclic_types:            0
% 2.36/0.98  sat_guarded_non_collapsed_types:        0
% 2.36/0.98  num_pure_diseq_elim:                    0
% 2.36/0.98  simp_replaced_by:                       0
% 2.36/0.98  res_preprocessed:                       115
% 2.36/0.98  prep_upred:                             0
% 2.36/0.98  prep_unflattend:                        14
% 2.36/0.98  smt_new_axioms:                         0
% 2.36/0.98  pred_elim_cands:                        3
% 2.36/0.98  pred_elim:                              7
% 2.36/0.98  pred_elim_cl:                           8
% 2.36/0.98  pred_elim_cycles:                       10
% 2.36/0.98  merged_defs:                            0
% 2.36/0.98  merged_defs_ncl:                        0
% 2.36/0.98  bin_hyper_res:                          0
% 2.36/0.98  prep_cycles:                            4
% 2.36/0.98  pred_elim_time:                         0.006
% 2.36/0.98  splitting_time:                         0.
% 2.36/0.98  sem_filter_time:                        0.
% 2.36/0.98  monotx_time:                            0.
% 2.36/0.98  subtype_inf_time:                       0.001
% 2.36/0.98  
% 2.36/0.98  ------ Problem properties
% 2.36/0.98  
% 2.36/0.98  clauses:                                18
% 2.36/0.98  conjectures:                            5
% 2.36/0.98  epr:                                    1
% 2.36/0.98  horn:                                   17
% 2.36/0.98  ground:                                 8
% 2.36/0.98  unary:                                  7
% 2.36/0.98  binary:                                 5
% 2.36/0.98  lits:                                   43
% 2.36/0.98  lits_eq:                                15
% 2.36/0.98  fd_pure:                                0
% 2.36/0.98  fd_pseudo:                              0
% 2.36/0.98  fd_cond:                                0
% 2.36/0.98  fd_pseudo_cond:                         1
% 2.36/0.98  ac_symbols:                             0
% 2.36/0.98  
% 2.36/0.98  ------ Propositional Solver
% 2.36/0.98  
% 2.36/0.98  prop_solver_calls:                      28
% 2.36/0.98  prop_fast_solver_calls:                 755
% 2.36/0.98  smt_solver_calls:                       0
% 2.36/0.98  smt_fast_solver_calls:                  0
% 2.36/0.98  prop_num_of_clauses:                    1027
% 2.36/0.98  prop_preprocess_simplified:             3637
% 2.36/0.98  prop_fo_subsumed:                       27
% 2.36/0.98  prop_solver_time:                       0.
% 2.36/0.98  smt_solver_time:                        0.
% 2.36/0.98  smt_fast_solver_time:                   0.
% 2.36/0.98  prop_fast_solver_time:                  0.
% 2.36/0.98  prop_unsat_core_time:                   0.
% 2.36/0.98  
% 2.36/0.98  ------ QBF
% 2.36/0.98  
% 2.36/0.98  qbf_q_res:                              0
% 2.36/0.98  qbf_num_tautologies:                    0
% 2.36/0.98  qbf_prep_cycles:                        0
% 2.36/0.98  
% 2.36/0.98  ------ BMC1
% 2.36/0.98  
% 2.36/0.98  bmc1_current_bound:                     -1
% 2.36/0.98  bmc1_last_solved_bound:                 -1
% 2.36/0.98  bmc1_unsat_core_size:                   -1
% 2.36/0.98  bmc1_unsat_core_parents_size:           -1
% 2.36/0.98  bmc1_merge_next_fun:                    0
% 2.36/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation
% 2.36/0.98  
% 2.36/0.98  inst_num_of_clauses:                    343
% 2.36/0.98  inst_num_in_passive:                    143
% 2.36/0.98  inst_num_in_active:                     166
% 2.36/0.98  inst_num_in_unprocessed:                34
% 2.36/0.98  inst_num_of_loops:                      210
% 2.36/0.98  inst_num_of_learning_restarts:          0
% 2.36/0.98  inst_num_moves_active_passive:          39
% 2.36/0.98  inst_lit_activity:                      0
% 2.36/0.98  inst_lit_activity_moves:                0
% 2.36/0.98  inst_num_tautologies:                   0
% 2.36/0.98  inst_num_prop_implied:                  0
% 2.36/0.98  inst_num_existing_simplified:           0
% 2.36/0.98  inst_num_eq_res_simplified:             0
% 2.36/0.98  inst_num_child_elim:                    0
% 2.36/0.98  inst_num_of_dismatching_blockings:      38
% 2.36/0.98  inst_num_of_non_proper_insts:           268
% 2.36/0.98  inst_num_of_duplicates:                 0
% 2.36/0.98  inst_inst_num_from_inst_to_res:         0
% 2.36/0.98  inst_dismatching_checking_time:         0.
% 2.36/0.98  
% 2.36/0.98  ------ Resolution
% 2.36/0.98  
% 2.36/0.98  res_num_of_clauses:                     0
% 2.36/0.98  res_num_in_passive:                     0
% 2.36/0.98  res_num_in_active:                      0
% 2.36/0.98  res_num_of_loops:                       119
% 2.36/0.98  res_forward_subset_subsumed:            36
% 2.36/0.98  res_backward_subset_subsumed:           0
% 2.36/0.98  res_forward_subsumed:                   0
% 2.36/0.98  res_backward_subsumed:                  0
% 2.36/0.98  res_forward_subsumption_resolution:     1
% 2.36/0.98  res_backward_subsumption_resolution:    0
% 2.36/0.98  res_clause_to_clause_subsumption:       84
% 2.36/0.98  res_orphan_elimination:                 0
% 2.36/0.98  res_tautology_del:                      31
% 2.36/0.98  res_num_eq_res_simplified:              0
% 2.36/0.98  res_num_sel_changes:                    0
% 2.36/0.98  res_moves_from_active_to_pass:          0
% 2.36/0.98  
% 2.36/0.98  ------ Superposition
% 2.36/0.98  
% 2.36/0.98  sup_time_total:                         0.
% 2.36/0.98  sup_time_generating:                    0.
% 2.36/0.98  sup_time_sim_full:                      0.
% 2.36/0.98  sup_time_sim_immed:                     0.
% 2.36/0.98  
% 2.36/0.98  sup_num_of_clauses:                     38
% 2.36/0.98  sup_num_in_active:                      29
% 2.36/0.98  sup_num_in_passive:                     9
% 2.36/0.98  sup_num_of_loops:                       41
% 2.36/0.98  sup_fw_superposition:                   13
% 2.36/0.98  sup_bw_superposition:                   19
% 2.36/0.98  sup_immediate_simplified:               12
% 2.36/0.98  sup_given_eliminated:                   0
% 2.36/0.98  comparisons_done:                       0
% 2.36/0.98  comparisons_avoided:                    1
% 2.36/0.98  
% 2.36/0.98  ------ Simplifications
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  sim_fw_subset_subsumed:                 6
% 2.36/0.98  sim_bw_subset_subsumed:                 1
% 2.36/0.98  sim_fw_subsumed:                        0
% 2.36/0.98  sim_bw_subsumed:                        0
% 2.36/0.98  sim_fw_subsumption_res:                 0
% 2.36/0.98  sim_bw_subsumption_res:                 0
% 2.36/0.98  sim_tautology_del:                      0
% 2.36/0.98  sim_eq_tautology_del:                   1
% 2.36/0.98  sim_eq_res_simp:                        1
% 2.36/0.98  sim_fw_demodulated:                     0
% 2.36/0.98  sim_bw_demodulated:                     13
% 2.36/0.98  sim_light_normalised:                   14
% 2.36/0.98  sim_joinable_taut:                      0
% 2.36/0.98  sim_joinable_simp:                      0
% 2.36/0.98  sim_ac_normalised:                      0
% 2.36/0.98  sim_smt_subsumption:                    0
% 2.36/0.98  
%------------------------------------------------------------------------------
