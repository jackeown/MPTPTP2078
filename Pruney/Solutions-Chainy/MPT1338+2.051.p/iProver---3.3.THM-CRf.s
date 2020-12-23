%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:09 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  141 (2117 expanded)
%              Number of clauses        :   88 ( 576 expanded)
%              Number of leaves         :   14 ( 644 expanded)
%              Depth                    :   19
%              Number of atoms          :  466 (15576 expanded)
%              Number of equality atoms :  210 (5405 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32,f31,f30])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f29,plain,(
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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_933,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_311,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_312,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_316,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_317,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_954,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_933,c_312,c_317])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_940,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1193,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_954,c_940])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_951,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_20,c_312,c_317])).

cnf(c_1633,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1193,c_951])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_365,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_366,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_370,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_23])).

cnf(c_371,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_931,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_1388,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_931])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_932,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_948,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_932,c_312,c_317])).

cnf(c_1391,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1388,c_948,c_954])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1015,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_18,c_312,c_317])).

cnf(c_1394,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1391,c_1015])).

cnf(c_1673,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1633,c_1394])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_438,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_23])).

cnf(c_443,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_929,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1480,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_929])).

cnf(c_1620,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_948,c_954])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_941,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1625,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1620,c_941])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_461,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_462,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_464,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_23])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_464])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_927,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1187,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_21,c_1090])).

cnf(c_1630,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1625,c_1187])).

cnf(c_2512,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1630,c_1633])).

cnf(c_2830,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1673,c_2512])).

cnf(c_1676,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1633,c_954])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_934,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2285,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_934])).

cnf(c_1271,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_954,c_941])).

cnf(c_2233,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1271,c_1633])).

cnf(c_2291,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2285,c_2233])).

cnf(c_1677,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1633,c_948])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_284,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_302,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_25])).

cnf(c_303,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_305,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_24])).

cnf(c_1679,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1633,c_305])).

cnf(c_2673,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_1677,c_1679])).

cnf(c_2832,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2830,c_2673])).

cnf(c_1626,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1620,c_940])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_475,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_476,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_478,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_23])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_478])).

cnf(c_516,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_928,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1705,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_21,c_1087])).

cnf(c_2510,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1626,c_1633,c_1705])).

cnf(c_2678,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2673,c_2510])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2832,c_2678])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:17:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.62/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/1.02  
% 2.62/1.02  ------  iProver source info
% 2.62/1.02  
% 2.62/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.62/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/1.02  git: non_committed_changes: false
% 2.62/1.02  git: last_make_outside_of_git: false
% 2.62/1.02  
% 2.62/1.02  ------ 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options
% 2.62/1.02  
% 2.62/1.02  --out_options                           all
% 2.62/1.02  --tptp_safe_out                         true
% 2.62/1.02  --problem_path                          ""
% 2.62/1.02  --include_path                          ""
% 2.62/1.02  --clausifier                            res/vclausify_rel
% 2.62/1.02  --clausifier_options                    --mode clausify
% 2.62/1.02  --stdin                                 false
% 2.62/1.02  --stats_out                             all
% 2.62/1.02  
% 2.62/1.02  ------ General Options
% 2.62/1.02  
% 2.62/1.02  --fof                                   false
% 2.62/1.02  --time_out_real                         305.
% 2.62/1.02  --time_out_virtual                      -1.
% 2.62/1.02  --symbol_type_check                     false
% 2.62/1.02  --clausify_out                          false
% 2.62/1.02  --sig_cnt_out                           false
% 2.62/1.02  --trig_cnt_out                          false
% 2.62/1.02  --trig_cnt_out_tolerance                1.
% 2.62/1.02  --trig_cnt_out_sk_spl                   false
% 2.62/1.02  --abstr_cl_out                          false
% 2.62/1.02  
% 2.62/1.02  ------ Global Options
% 2.62/1.02  
% 2.62/1.02  --schedule                              default
% 2.62/1.02  --add_important_lit                     false
% 2.62/1.02  --prop_solver_per_cl                    1000
% 2.62/1.02  --min_unsat_core                        false
% 2.62/1.02  --soft_assumptions                      false
% 2.62/1.02  --soft_lemma_size                       3
% 2.62/1.02  --prop_impl_unit_size                   0
% 2.62/1.02  --prop_impl_unit                        []
% 2.62/1.02  --share_sel_clauses                     true
% 2.62/1.02  --reset_solvers                         false
% 2.62/1.02  --bc_imp_inh                            [conj_cone]
% 2.62/1.02  --conj_cone_tolerance                   3.
% 2.62/1.02  --extra_neg_conj                        none
% 2.62/1.02  --large_theory_mode                     true
% 2.62/1.02  --prolific_symb_bound                   200
% 2.62/1.02  --lt_threshold                          2000
% 2.62/1.02  --clause_weak_htbl                      true
% 2.62/1.02  --gc_record_bc_elim                     false
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing Options
% 2.62/1.02  
% 2.62/1.02  --preprocessing_flag                    true
% 2.62/1.02  --time_out_prep_mult                    0.1
% 2.62/1.02  --splitting_mode                        input
% 2.62/1.02  --splitting_grd                         true
% 2.62/1.02  --splitting_cvd                         false
% 2.62/1.02  --splitting_cvd_svl                     false
% 2.62/1.02  --splitting_nvd                         32
% 2.62/1.02  --sub_typing                            true
% 2.62/1.02  --prep_gs_sim                           true
% 2.62/1.02  --prep_unflatten                        true
% 2.62/1.02  --prep_res_sim                          true
% 2.62/1.02  --prep_upred                            true
% 2.62/1.02  --prep_sem_filter                       exhaustive
% 2.62/1.02  --prep_sem_filter_out                   false
% 2.62/1.02  --pred_elim                             true
% 2.62/1.02  --res_sim_input                         true
% 2.62/1.02  --eq_ax_congr_red                       true
% 2.62/1.02  --pure_diseq_elim                       true
% 2.62/1.02  --brand_transform                       false
% 2.62/1.02  --non_eq_to_eq                          false
% 2.62/1.02  --prep_def_merge                        true
% 2.62/1.02  --prep_def_merge_prop_impl              false
% 2.62/1.02  --prep_def_merge_mbd                    true
% 2.62/1.02  --prep_def_merge_tr_red                 false
% 2.62/1.02  --prep_def_merge_tr_cl                  false
% 2.62/1.02  --smt_preprocessing                     true
% 2.62/1.02  --smt_ac_axioms                         fast
% 2.62/1.02  --preprocessed_out                      false
% 2.62/1.02  --preprocessed_stats                    false
% 2.62/1.02  
% 2.62/1.02  ------ Abstraction refinement Options
% 2.62/1.02  
% 2.62/1.02  --abstr_ref                             []
% 2.62/1.02  --abstr_ref_prep                        false
% 2.62/1.02  --abstr_ref_until_sat                   false
% 2.62/1.02  --abstr_ref_sig_restrict                funpre
% 2.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.02  --abstr_ref_under                       []
% 2.62/1.02  
% 2.62/1.02  ------ SAT Options
% 2.62/1.02  
% 2.62/1.02  --sat_mode                              false
% 2.62/1.02  --sat_fm_restart_options                ""
% 2.62/1.02  --sat_gr_def                            false
% 2.62/1.02  --sat_epr_types                         true
% 2.62/1.02  --sat_non_cyclic_types                  false
% 2.62/1.02  --sat_finite_models                     false
% 2.62/1.02  --sat_fm_lemmas                         false
% 2.62/1.02  --sat_fm_prep                           false
% 2.62/1.02  --sat_fm_uc_incr                        true
% 2.62/1.02  --sat_out_model                         small
% 2.62/1.02  --sat_out_clauses                       false
% 2.62/1.02  
% 2.62/1.02  ------ QBF Options
% 2.62/1.02  
% 2.62/1.02  --qbf_mode                              false
% 2.62/1.02  --qbf_elim_univ                         false
% 2.62/1.02  --qbf_dom_inst                          none
% 2.62/1.02  --qbf_dom_pre_inst                      false
% 2.62/1.02  --qbf_sk_in                             false
% 2.62/1.02  --qbf_pred_elim                         true
% 2.62/1.02  --qbf_split                             512
% 2.62/1.02  
% 2.62/1.02  ------ BMC1 Options
% 2.62/1.02  
% 2.62/1.02  --bmc1_incremental                      false
% 2.62/1.02  --bmc1_axioms                           reachable_all
% 2.62/1.02  --bmc1_min_bound                        0
% 2.62/1.02  --bmc1_max_bound                        -1
% 2.62/1.02  --bmc1_max_bound_default                -1
% 2.62/1.02  --bmc1_symbol_reachability              true
% 2.62/1.02  --bmc1_property_lemmas                  false
% 2.62/1.02  --bmc1_k_induction                      false
% 2.62/1.02  --bmc1_non_equiv_states                 false
% 2.62/1.02  --bmc1_deadlock                         false
% 2.62/1.02  --bmc1_ucm                              false
% 2.62/1.02  --bmc1_add_unsat_core                   none
% 2.62/1.02  --bmc1_unsat_core_children              false
% 2.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.02  --bmc1_out_stat                         full
% 2.62/1.02  --bmc1_ground_init                      false
% 2.62/1.02  --bmc1_pre_inst_next_state              false
% 2.62/1.02  --bmc1_pre_inst_state                   false
% 2.62/1.02  --bmc1_pre_inst_reach_state             false
% 2.62/1.02  --bmc1_out_unsat_core                   false
% 2.62/1.02  --bmc1_aig_witness_out                  false
% 2.62/1.02  --bmc1_verbose                          false
% 2.62/1.02  --bmc1_dump_clauses_tptp                false
% 2.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.02  --bmc1_dump_file                        -
% 2.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.02  --bmc1_ucm_extend_mode                  1
% 2.62/1.02  --bmc1_ucm_init_mode                    2
% 2.62/1.02  --bmc1_ucm_cone_mode                    none
% 2.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.02  --bmc1_ucm_relax_model                  4
% 2.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.02  --bmc1_ucm_layered_model                none
% 2.62/1.02  --bmc1_ucm_max_lemma_size               10
% 2.62/1.02  
% 2.62/1.02  ------ AIG Options
% 2.62/1.02  
% 2.62/1.02  --aig_mode                              false
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation Options
% 2.62/1.02  
% 2.62/1.02  --instantiation_flag                    true
% 2.62/1.02  --inst_sos_flag                         false
% 2.62/1.02  --inst_sos_phase                        true
% 2.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel_side                     num_symb
% 2.62/1.02  --inst_solver_per_active                1400
% 2.62/1.02  --inst_solver_calls_frac                1.
% 2.62/1.02  --inst_passive_queue_type               priority_queues
% 2.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.02  --inst_passive_queues_freq              [25;2]
% 2.62/1.02  --inst_dismatching                      true
% 2.62/1.02  --inst_eager_unprocessed_to_passive     true
% 2.62/1.02  --inst_prop_sim_given                   true
% 2.62/1.02  --inst_prop_sim_new                     false
% 2.62/1.02  --inst_subs_new                         false
% 2.62/1.02  --inst_eq_res_simp                      false
% 2.62/1.02  --inst_subs_given                       false
% 2.62/1.02  --inst_orphan_elimination               true
% 2.62/1.02  --inst_learning_loop_flag               true
% 2.62/1.02  --inst_learning_start                   3000
% 2.62/1.02  --inst_learning_factor                  2
% 2.62/1.02  --inst_start_prop_sim_after_learn       3
% 2.62/1.02  --inst_sel_renew                        solver
% 2.62/1.02  --inst_lit_activity_flag                true
% 2.62/1.02  --inst_restr_to_given                   false
% 2.62/1.02  --inst_activity_threshold               500
% 2.62/1.02  --inst_out_proof                        true
% 2.62/1.02  
% 2.62/1.02  ------ Resolution Options
% 2.62/1.02  
% 2.62/1.02  --resolution_flag                       true
% 2.62/1.02  --res_lit_sel                           adaptive
% 2.62/1.02  --res_lit_sel_side                      none
% 2.62/1.02  --res_ordering                          kbo
% 2.62/1.02  --res_to_prop_solver                    active
% 2.62/1.02  --res_prop_simpl_new                    false
% 2.62/1.02  --res_prop_simpl_given                  true
% 2.62/1.02  --res_passive_queue_type                priority_queues
% 2.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.02  --res_passive_queues_freq               [15;5]
% 2.62/1.02  --res_forward_subs                      full
% 2.62/1.02  --res_backward_subs                     full
% 2.62/1.02  --res_forward_subs_resolution           true
% 2.62/1.02  --res_backward_subs_resolution          true
% 2.62/1.02  --res_orphan_elimination                true
% 2.62/1.02  --res_time_limit                        2.
% 2.62/1.02  --res_out_proof                         true
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Options
% 2.62/1.02  
% 2.62/1.02  --superposition_flag                    true
% 2.62/1.02  --sup_passive_queue_type                priority_queues
% 2.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.02  --demod_completeness_check              fast
% 2.62/1.02  --demod_use_ground                      true
% 2.62/1.02  --sup_to_prop_solver                    passive
% 2.62/1.02  --sup_prop_simpl_new                    true
% 2.62/1.02  --sup_prop_simpl_given                  true
% 2.62/1.02  --sup_fun_splitting                     false
% 2.62/1.02  --sup_smt_interval                      50000
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Simplification Setup
% 2.62/1.02  
% 2.62/1.02  --sup_indices_passive                   []
% 2.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_full_bw                           [BwDemod]
% 2.62/1.02  --sup_immed_triv                        [TrivRules]
% 2.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_immed_bw_main                     []
% 2.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  
% 2.62/1.02  ------ Combination Options
% 2.62/1.02  
% 2.62/1.02  --comb_res_mult                         3
% 2.62/1.02  --comb_sup_mult                         2
% 2.62/1.02  --comb_inst_mult                        10
% 2.62/1.02  
% 2.62/1.02  ------ Debug Options
% 2.62/1.02  
% 2.62/1.02  --dbg_backtrace                         false
% 2.62/1.02  --dbg_dump_prop_clauses                 false
% 2.62/1.02  --dbg_dump_prop_clauses_file            -
% 2.62/1.02  --dbg_out_stat                          false
% 2.62/1.02  ------ Parsing...
% 2.62/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/1.02  ------ Proving...
% 2.62/1.02  ------ Problem Properties 
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  clauses                                 20
% 2.62/1.02  conjectures                             4
% 2.62/1.02  EPR                                     0
% 2.62/1.02  Horn                                    16
% 2.62/1.02  unary                                   6
% 2.62/1.02  binary                                  5
% 2.62/1.02  lits                                    49
% 2.62/1.02  lits eq                                 23
% 2.62/1.02  fd_pure                                 0
% 2.62/1.02  fd_pseudo                               0
% 2.62/1.02  fd_cond                                 3
% 2.62/1.02  fd_pseudo_cond                          0
% 2.62/1.02  AC symbols                              0
% 2.62/1.02  
% 2.62/1.02  ------ Schedule dynamic 5 is on 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  ------ 
% 2.62/1.02  Current options:
% 2.62/1.02  ------ 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options
% 2.62/1.02  
% 2.62/1.02  --out_options                           all
% 2.62/1.02  --tptp_safe_out                         true
% 2.62/1.02  --problem_path                          ""
% 2.62/1.02  --include_path                          ""
% 2.62/1.02  --clausifier                            res/vclausify_rel
% 2.62/1.02  --clausifier_options                    --mode clausify
% 2.62/1.02  --stdin                                 false
% 2.62/1.02  --stats_out                             all
% 2.62/1.02  
% 2.62/1.02  ------ General Options
% 2.62/1.02  
% 2.62/1.02  --fof                                   false
% 2.62/1.02  --time_out_real                         305.
% 2.62/1.02  --time_out_virtual                      -1.
% 2.62/1.02  --symbol_type_check                     false
% 2.62/1.02  --clausify_out                          false
% 2.62/1.02  --sig_cnt_out                           false
% 2.62/1.02  --trig_cnt_out                          false
% 2.62/1.02  --trig_cnt_out_tolerance                1.
% 2.62/1.02  --trig_cnt_out_sk_spl                   false
% 2.62/1.02  --abstr_cl_out                          false
% 2.62/1.02  
% 2.62/1.02  ------ Global Options
% 2.62/1.02  
% 2.62/1.02  --schedule                              default
% 2.62/1.02  --add_important_lit                     false
% 2.62/1.02  --prop_solver_per_cl                    1000
% 2.62/1.02  --min_unsat_core                        false
% 2.62/1.02  --soft_assumptions                      false
% 2.62/1.02  --soft_lemma_size                       3
% 2.62/1.02  --prop_impl_unit_size                   0
% 2.62/1.02  --prop_impl_unit                        []
% 2.62/1.02  --share_sel_clauses                     true
% 2.62/1.02  --reset_solvers                         false
% 2.62/1.02  --bc_imp_inh                            [conj_cone]
% 2.62/1.02  --conj_cone_tolerance                   3.
% 2.62/1.02  --extra_neg_conj                        none
% 2.62/1.02  --large_theory_mode                     true
% 2.62/1.02  --prolific_symb_bound                   200
% 2.62/1.02  --lt_threshold                          2000
% 2.62/1.02  --clause_weak_htbl                      true
% 2.62/1.02  --gc_record_bc_elim                     false
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing Options
% 2.62/1.02  
% 2.62/1.02  --preprocessing_flag                    true
% 2.62/1.02  --time_out_prep_mult                    0.1
% 2.62/1.02  --splitting_mode                        input
% 2.62/1.02  --splitting_grd                         true
% 2.62/1.02  --splitting_cvd                         false
% 2.62/1.02  --splitting_cvd_svl                     false
% 2.62/1.02  --splitting_nvd                         32
% 2.62/1.02  --sub_typing                            true
% 2.62/1.02  --prep_gs_sim                           true
% 2.62/1.02  --prep_unflatten                        true
% 2.62/1.02  --prep_res_sim                          true
% 2.62/1.02  --prep_upred                            true
% 2.62/1.02  --prep_sem_filter                       exhaustive
% 2.62/1.02  --prep_sem_filter_out                   false
% 2.62/1.02  --pred_elim                             true
% 2.62/1.02  --res_sim_input                         true
% 2.62/1.02  --eq_ax_congr_red                       true
% 2.62/1.02  --pure_diseq_elim                       true
% 2.62/1.02  --brand_transform                       false
% 2.62/1.02  --non_eq_to_eq                          false
% 2.62/1.02  --prep_def_merge                        true
% 2.62/1.02  --prep_def_merge_prop_impl              false
% 2.62/1.02  --prep_def_merge_mbd                    true
% 2.62/1.02  --prep_def_merge_tr_red                 false
% 2.62/1.02  --prep_def_merge_tr_cl                  false
% 2.62/1.02  --smt_preprocessing                     true
% 2.62/1.02  --smt_ac_axioms                         fast
% 2.62/1.02  --preprocessed_out                      false
% 2.62/1.02  --preprocessed_stats                    false
% 2.62/1.02  
% 2.62/1.02  ------ Abstraction refinement Options
% 2.62/1.02  
% 2.62/1.02  --abstr_ref                             []
% 2.62/1.02  --abstr_ref_prep                        false
% 2.62/1.02  --abstr_ref_until_sat                   false
% 2.62/1.02  --abstr_ref_sig_restrict                funpre
% 2.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.02  --abstr_ref_under                       []
% 2.62/1.02  
% 2.62/1.02  ------ SAT Options
% 2.62/1.02  
% 2.62/1.02  --sat_mode                              false
% 2.62/1.02  --sat_fm_restart_options                ""
% 2.62/1.02  --sat_gr_def                            false
% 2.62/1.02  --sat_epr_types                         true
% 2.62/1.02  --sat_non_cyclic_types                  false
% 2.62/1.02  --sat_finite_models                     false
% 2.62/1.02  --sat_fm_lemmas                         false
% 2.62/1.02  --sat_fm_prep                           false
% 2.62/1.02  --sat_fm_uc_incr                        true
% 2.62/1.02  --sat_out_model                         small
% 2.62/1.02  --sat_out_clauses                       false
% 2.62/1.02  
% 2.62/1.02  ------ QBF Options
% 2.62/1.02  
% 2.62/1.02  --qbf_mode                              false
% 2.62/1.02  --qbf_elim_univ                         false
% 2.62/1.02  --qbf_dom_inst                          none
% 2.62/1.02  --qbf_dom_pre_inst                      false
% 2.62/1.02  --qbf_sk_in                             false
% 2.62/1.02  --qbf_pred_elim                         true
% 2.62/1.02  --qbf_split                             512
% 2.62/1.02  
% 2.62/1.02  ------ BMC1 Options
% 2.62/1.02  
% 2.62/1.02  --bmc1_incremental                      false
% 2.62/1.02  --bmc1_axioms                           reachable_all
% 2.62/1.02  --bmc1_min_bound                        0
% 2.62/1.02  --bmc1_max_bound                        -1
% 2.62/1.02  --bmc1_max_bound_default                -1
% 2.62/1.02  --bmc1_symbol_reachability              true
% 2.62/1.02  --bmc1_property_lemmas                  false
% 2.62/1.02  --bmc1_k_induction                      false
% 2.62/1.02  --bmc1_non_equiv_states                 false
% 2.62/1.02  --bmc1_deadlock                         false
% 2.62/1.02  --bmc1_ucm                              false
% 2.62/1.02  --bmc1_add_unsat_core                   none
% 2.62/1.02  --bmc1_unsat_core_children              false
% 2.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.02  --bmc1_out_stat                         full
% 2.62/1.02  --bmc1_ground_init                      false
% 2.62/1.02  --bmc1_pre_inst_next_state              false
% 2.62/1.02  --bmc1_pre_inst_state                   false
% 2.62/1.02  --bmc1_pre_inst_reach_state             false
% 2.62/1.02  --bmc1_out_unsat_core                   false
% 2.62/1.02  --bmc1_aig_witness_out                  false
% 2.62/1.02  --bmc1_verbose                          false
% 2.62/1.02  --bmc1_dump_clauses_tptp                false
% 2.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.02  --bmc1_dump_file                        -
% 2.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.02  --bmc1_ucm_extend_mode                  1
% 2.62/1.02  --bmc1_ucm_init_mode                    2
% 2.62/1.02  --bmc1_ucm_cone_mode                    none
% 2.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.02  --bmc1_ucm_relax_model                  4
% 2.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.02  --bmc1_ucm_layered_model                none
% 2.62/1.02  --bmc1_ucm_max_lemma_size               10
% 2.62/1.02  
% 2.62/1.02  ------ AIG Options
% 2.62/1.02  
% 2.62/1.02  --aig_mode                              false
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation Options
% 2.62/1.02  
% 2.62/1.02  --instantiation_flag                    true
% 2.62/1.02  --inst_sos_flag                         false
% 2.62/1.02  --inst_sos_phase                        true
% 2.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel_side                     none
% 2.62/1.02  --inst_solver_per_active                1400
% 2.62/1.02  --inst_solver_calls_frac                1.
% 2.62/1.02  --inst_passive_queue_type               priority_queues
% 2.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.02  --inst_passive_queues_freq              [25;2]
% 2.62/1.02  --inst_dismatching                      true
% 2.62/1.02  --inst_eager_unprocessed_to_passive     true
% 2.62/1.02  --inst_prop_sim_given                   true
% 2.62/1.02  --inst_prop_sim_new                     false
% 2.62/1.02  --inst_subs_new                         false
% 2.62/1.02  --inst_eq_res_simp                      false
% 2.62/1.02  --inst_subs_given                       false
% 2.62/1.02  --inst_orphan_elimination               true
% 2.62/1.02  --inst_learning_loop_flag               true
% 2.62/1.02  --inst_learning_start                   3000
% 2.62/1.02  --inst_learning_factor                  2
% 2.62/1.02  --inst_start_prop_sim_after_learn       3
% 2.62/1.02  --inst_sel_renew                        solver
% 2.62/1.02  --inst_lit_activity_flag                true
% 2.62/1.02  --inst_restr_to_given                   false
% 2.62/1.02  --inst_activity_threshold               500
% 2.62/1.02  --inst_out_proof                        true
% 2.62/1.02  
% 2.62/1.02  ------ Resolution Options
% 2.62/1.02  
% 2.62/1.02  --resolution_flag                       false
% 2.62/1.02  --res_lit_sel                           adaptive
% 2.62/1.02  --res_lit_sel_side                      none
% 2.62/1.02  --res_ordering                          kbo
% 2.62/1.02  --res_to_prop_solver                    active
% 2.62/1.02  --res_prop_simpl_new                    false
% 2.62/1.02  --res_prop_simpl_given                  true
% 2.62/1.02  --res_passive_queue_type                priority_queues
% 2.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.02  --res_passive_queues_freq               [15;5]
% 2.62/1.02  --res_forward_subs                      full
% 2.62/1.02  --res_backward_subs                     full
% 2.62/1.02  --res_forward_subs_resolution           true
% 2.62/1.02  --res_backward_subs_resolution          true
% 2.62/1.02  --res_orphan_elimination                true
% 2.62/1.02  --res_time_limit                        2.
% 2.62/1.02  --res_out_proof                         true
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Options
% 2.62/1.02  
% 2.62/1.02  --superposition_flag                    true
% 2.62/1.02  --sup_passive_queue_type                priority_queues
% 2.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.02  --demod_completeness_check              fast
% 2.62/1.02  --demod_use_ground                      true
% 2.62/1.02  --sup_to_prop_solver                    passive
% 2.62/1.02  --sup_prop_simpl_new                    true
% 2.62/1.02  --sup_prop_simpl_given                  true
% 2.62/1.02  --sup_fun_splitting                     false
% 2.62/1.02  --sup_smt_interval                      50000
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Simplification Setup
% 2.62/1.02  
% 2.62/1.02  --sup_indices_passive                   []
% 2.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_full_bw                           [BwDemod]
% 2.62/1.02  --sup_immed_triv                        [TrivRules]
% 2.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_immed_bw_main                     []
% 2.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  
% 2.62/1.02  ------ Combination Options
% 2.62/1.02  
% 2.62/1.02  --comb_res_mult                         3
% 2.62/1.02  --comb_sup_mult                         2
% 2.62/1.02  --comb_inst_mult                        10
% 2.62/1.02  
% 2.62/1.02  ------ Debug Options
% 2.62/1.02  
% 2.62/1.02  --dbg_backtrace                         false
% 2.62/1.02  --dbg_dump_prop_clauses                 false
% 2.62/1.02  --dbg_dump_prop_clauses_file            -
% 2.62/1.02  --dbg_out_stat                          false
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  ------ Proving...
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  % SZS status Theorem for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  fof(f11,conjecture,(
% 2.62/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f12,negated_conjecture,(
% 2.62/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.62/1.02    inference(negated_conjecture,[],[f11])).
% 2.62/1.02  
% 2.62/1.02  fof(f27,plain,(
% 2.62/1.02    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.62/1.02    inference(ennf_transformation,[],[f12])).
% 2.62/1.02  
% 2.62/1.02  fof(f28,plain,(
% 2.62/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.62/1.02    inference(flattening,[],[f27])).
% 2.62/1.02  
% 2.62/1.02  fof(f32,plain,(
% 2.62/1.02    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.62/1.02    introduced(choice_axiom,[])).
% 2.62/1.02  
% 2.62/1.02  fof(f31,plain,(
% 2.62/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.62/1.02    introduced(choice_axiom,[])).
% 2.62/1.02  
% 2.62/1.02  fof(f30,plain,(
% 2.62/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.62/1.02    introduced(choice_axiom,[])).
% 2.62/1.02  
% 2.62/1.02  fof(f33,plain,(
% 2.62/1.02    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32,f31,f30])).
% 2.62/1.02  
% 2.62/1.02  fof(f57,plain,(
% 2.62/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f8,axiom,(
% 2.62/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f22,plain,(
% 2.62/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.62/1.02    inference(ennf_transformation,[],[f8])).
% 2.62/1.02  
% 2.62/1.02  fof(f49,plain,(
% 2.62/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f22])).
% 2.62/1.02  
% 2.62/1.02  fof(f54,plain,(
% 2.62/1.02    l1_struct_0(sK1)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f52,plain,(
% 2.62/1.02    l1_struct_0(sK0)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f5,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f17,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f5])).
% 2.62/1.02  
% 2.62/1.02  fof(f39,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f17])).
% 2.62/1.02  
% 2.62/1.02  fof(f58,plain,(
% 2.62/1.02    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f10,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f25,plain,(
% 2.62/1.02    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.62/1.02    inference(ennf_transformation,[],[f10])).
% 2.62/1.02  
% 2.62/1.02  fof(f26,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/1.02    inference(flattening,[],[f25])).
% 2.62/1.02  
% 2.62/1.02  fof(f51,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f26])).
% 2.62/1.02  
% 2.62/1.02  fof(f59,plain,(
% 2.62/1.02    v2_funct_1(sK2)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f55,plain,(
% 2.62/1.02    v1_funct_1(sK2)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f56,plain,(
% 2.62/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f60,plain,(
% 2.62/1.02    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f7,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f20,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.62/1.02    inference(ennf_transformation,[],[f7])).
% 2.62/1.02  
% 2.62/1.02  fof(f21,plain,(
% 2.62/1.02    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/1.02    inference(flattening,[],[f20])).
% 2.62/1.02  
% 2.62/1.02  fof(f48,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f21])).
% 2.62/1.02  
% 2.62/1.02  fof(f4,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f16,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f4])).
% 2.62/1.02  
% 2.62/1.02  fof(f38,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f16])).
% 2.62/1.02  
% 2.62/1.02  fof(f3,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f15,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f3])).
% 2.62/1.02  
% 2.62/1.02  fof(f37,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f15])).
% 2.62/1.02  
% 2.62/1.02  fof(f2,axiom,(
% 2.62/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f13,plain,(
% 2.62/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/1.02    inference(ennf_transformation,[],[f2])).
% 2.62/1.02  
% 2.62/1.02  fof(f14,plain,(
% 2.62/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/1.02    inference(flattening,[],[f13])).
% 2.62/1.02  
% 2.62/1.02  fof(f35,plain,(
% 2.62/1.02    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f14])).
% 2.62/1.02  
% 2.62/1.02  fof(f6,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f18,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f6])).
% 2.62/1.02  
% 2.62/1.02  fof(f19,plain,(
% 2.62/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(flattening,[],[f18])).
% 2.62/1.02  
% 2.62/1.02  fof(f29,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(nnf_transformation,[],[f19])).
% 2.62/1.02  
% 2.62/1.02  fof(f40,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f29])).
% 2.62/1.02  
% 2.62/1.02  fof(f1,axiom,(
% 2.62/1.02    v1_xboole_0(k1_xboole_0)),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f34,plain,(
% 2.62/1.02    v1_xboole_0(k1_xboole_0)),
% 2.62/1.02    inference(cnf_transformation,[],[f1])).
% 2.62/1.02  
% 2.62/1.02  fof(f9,axiom,(
% 2.62/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f23,plain,(
% 2.62/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.62/1.02    inference(ennf_transformation,[],[f9])).
% 2.62/1.02  
% 2.62/1.02  fof(f24,plain,(
% 2.62/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.62/1.02    inference(flattening,[],[f23])).
% 2.62/1.02  
% 2.62/1.02  fof(f50,plain,(
% 2.62/1.02    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f24])).
% 2.62/1.02  
% 2.62/1.02  fof(f53,plain,(
% 2.62/1.02    ~v2_struct_0(sK1)),
% 2.62/1.02    inference(cnf_transformation,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f36,plain,(
% 2.62/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f14])).
% 2.62/1.02  
% 2.62/1.02  cnf(c_21,negated_conjecture,
% 2.62/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.62/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_933,plain,
% 2.62/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_15,plain,
% 2.62/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_24,negated_conjecture,
% 2.62/1.02      ( l1_struct_0(sK1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_311,plain,
% 2.62/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_312,plain,
% 2.62/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_311]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_26,negated_conjecture,
% 2.62/1.02      ( l1_struct_0(sK0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_316,plain,
% 2.62/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_317,plain,
% 2.62/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_316]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_954,plain,
% 2.62/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_933,c_312,c_317]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_5,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_940,plain,
% 2.62/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.62/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1193,plain,
% 2.62/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_954,c_940]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_20,negated_conjecture,
% 2.62/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_951,plain,
% 2.62/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_20,c_312,c_317]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1633,plain,
% 2.62/1.02      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1193,c_951]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_17,plain,
% 2.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | ~ v2_funct_1(X0)
% 2.62/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.62/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.62/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_19,negated_conjecture,
% 2.62/1.02      ( v2_funct_1(sK2) ),
% 2.62/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_365,plain,
% 2.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.62/1.02      | k2_relset_1(X1,X2,X0) != X2
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_366,plain,
% 2.62/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | ~ v1_funct_1(sK2)
% 2.62/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_365]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_23,negated_conjecture,
% 2.62/1.02      ( v1_funct_1(sK2) ),
% 2.62/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_370,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_366,c_23]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_371,plain,
% 2.62/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(renaming,[status(thm)],[c_370]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_931,plain,
% 2.62/1.02      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 2.62/1.02      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1388,plain,
% 2.62/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.62/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_951,c_931]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_22,negated_conjecture,
% 2.62/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.62/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_932,plain,
% 2.62/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_948,plain,
% 2.62/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_932,c_312,c_317]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1391,plain,
% 2.62/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_1388,c_948,c_954]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_18,negated_conjecture,
% 2.62/1.02      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.62/1.02      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1015,plain,
% 2.62/1.02      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.62/1.02      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_18,c_312,c_317]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1394,plain,
% 2.62/1.02      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.62/1.02      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1391,c_1015]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1673,plain,
% 2.62/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.62/1.02      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1633,c_1394]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_12,plain,
% 2.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | ~ v2_funct_1(X0)
% 2.62/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.62/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_437,plain,
% 2.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | k2_relset_1(X1,X2,X0) != X2
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_438,plain,
% 2.62/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.62/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | ~ v1_funct_1(sK2)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_437]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_442,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.62/1.02      | ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_438,c_23]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_443,plain,
% 2.62/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.62/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.62/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.62/1.02      inference(renaming,[status(thm)],[c_442]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_929,plain,
% 2.62/1.02      ( k2_relset_1(X0,X1,sK2) != X1
% 2.62/1.02      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.62/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1480,plain,
% 2.62/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.62/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_951,c_929]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1620,plain,
% 2.62/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_1480,c_948,c_954]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_4,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_941,plain,
% 2.62/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.62/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1625,plain,
% 2.62/1.02      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_1620,c_941]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_3,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | v1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2,plain,
% 2.62/1.02      ( ~ v1_relat_1(X0)
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | ~ v2_funct_1(X0)
% 2.62/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_461,plain,
% 2.62/1.02      ( ~ v1_relat_1(X0)
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_462,plain,
% 2.62/1.02      ( ~ v1_relat_1(sK2)
% 2.62/1.02      | ~ v1_funct_1(sK2)
% 2.62/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_461]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_464,plain,
% 2.62/1.02      ( ~ v1_relat_1(sK2)
% 2.62/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_462,c_23]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_527,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_464]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_528,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_527]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_927,plain,
% 2.62/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1090,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(instantiation,[status(thm)],[c_528]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1187,plain,
% 2.62/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_927,c_21,c_1090]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1630,plain,
% 2.62/1.02      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_1625,c_1187]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2512,plain,
% 2.62/1.02      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_1630,c_1633]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2830,plain,
% 2.62/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_1673,c_2512]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1676,plain,
% 2.62/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1633,c_954]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_11,plain,
% 2.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.62/1.02      | k1_xboole_0 = X2 ),
% 2.62/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_934,plain,
% 2.62/1.02      ( k1_relset_1(X0,X1,X2) = X0
% 2.62/1.02      | k1_xboole_0 = X1
% 2.62/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.62/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2285,plain,
% 2.62/1.02      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 2.62/1.02      | k2_relat_1(sK2) = k1_xboole_0
% 2.62/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_1676,c_934]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1271,plain,
% 2.62/1.02      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_954,c_941]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2233,plain,
% 2.62/1.02      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_1271,c_1633]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2291,plain,
% 2.62/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/1.02      | k2_relat_1(sK2) = k1_xboole_0
% 2.62/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_2285,c_2233]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1677,plain,
% 2.62/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1633,c_948]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_0,plain,
% 2.62/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_16,plain,
% 2.62/1.02      ( v2_struct_0(X0)
% 2.62/1.02      | ~ l1_struct_0(X0)
% 2.62/1.02      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.62/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_284,plain,
% 2.62/1.02      ( v2_struct_0(X0)
% 2.62/1.02      | ~ l1_struct_0(X0)
% 2.62/1.02      | k2_struct_0(X0) != k1_xboole_0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_25,negated_conjecture,
% 2.62/1.02      ( ~ v2_struct_0(sK1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_302,plain,
% 2.62/1.02      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_284,c_25]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_303,plain,
% 2.62/1.02      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_302]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_305,plain,
% 2.62/1.02      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_303,c_24]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1679,plain,
% 2.62/1.02      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_1633,c_305]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2673,plain,
% 2.62/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_2291,c_1677,c_1679]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2832,plain,
% 2.62/1.02      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_2830,c_2673]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1626,plain,
% 2.62/1.02      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_1620,c_940]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1,plain,
% 2.62/1.02      ( ~ v1_relat_1(X0)
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | ~ v2_funct_1(X0)
% 2.62/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_475,plain,
% 2.62/1.02      ( ~ v1_relat_1(X0)
% 2.62/1.02      | ~ v1_funct_1(X0)
% 2.62/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_476,plain,
% 2.62/1.02      ( ~ v1_relat_1(sK2)
% 2.62/1.02      | ~ v1_funct_1(sK2)
% 2.62/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_475]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_478,plain,
% 2.62/1.02      ( ~ v1_relat_1(sK2)
% 2.62/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_476,c_23]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_515,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.62/1.02      | sK2 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_478]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_516,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_515]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_928,plain,
% 2.62/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.62/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1087,plain,
% 2.62/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(instantiation,[status(thm)],[c_516]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1705,plain,
% 2.62/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_928,c_21,c_1087]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2510,plain,
% 2.62/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_1626,c_1633,c_1705]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2678,plain,
% 2.62/1.02      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_2673,c_2510]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(contradiction,plain,
% 2.62/1.02      ( $false ),
% 2.62/1.02      inference(minisat,[status(thm)],[c_2832,c_2678]) ).
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  ------                               Statistics
% 2.62/1.02  
% 2.62/1.02  ------ General
% 2.62/1.02  
% 2.62/1.02  abstr_ref_over_cycles:                  0
% 2.62/1.02  abstr_ref_under_cycles:                 0
% 2.62/1.02  gc_basic_clause_elim:                   0
% 2.62/1.02  forced_gc_time:                         0
% 2.62/1.02  parsing_time:                           0.021
% 2.62/1.02  unif_index_cands_time:                  0.
% 2.62/1.02  unif_index_add_time:                    0.
% 2.62/1.02  orderings_time:                         0.
% 2.62/1.02  out_proof_time:                         0.018
% 2.62/1.02  total_time:                             0.165
% 2.62/1.02  num_of_symbols:                         53
% 2.62/1.02  num_of_terms:                           2866
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing
% 2.62/1.02  
% 2.62/1.02  num_of_splits:                          0
% 2.62/1.02  num_of_split_atoms:                     0
% 2.62/1.02  num_of_reused_defs:                     0
% 2.62/1.02  num_eq_ax_congr_red:                    2
% 2.62/1.02  num_of_sem_filtered_clauses:            1
% 2.62/1.02  num_of_subtypes:                        0
% 2.62/1.02  monotx_restored_types:                  0
% 2.62/1.02  sat_num_of_epr_types:                   0
% 2.62/1.02  sat_num_of_non_cyclic_types:            0
% 2.62/1.02  sat_guarded_non_collapsed_types:        0
% 2.62/1.02  num_pure_diseq_elim:                    0
% 2.62/1.02  simp_replaced_by:                       0
% 2.62/1.02  res_preprocessed:                       116
% 2.62/1.02  prep_upred:                             0
% 2.62/1.02  prep_unflattend:                        11
% 2.62/1.02  smt_new_axioms:                         0
% 2.62/1.02  pred_elim_cands:                        2
% 2.62/1.02  pred_elim:                              6
% 2.62/1.02  pred_elim_cl:                           7
% 2.62/1.02  pred_elim_cycles:                       9
% 2.62/1.02  merged_defs:                            0
% 2.62/1.02  merged_defs_ncl:                        0
% 2.62/1.02  bin_hyper_res:                          0
% 2.62/1.02  prep_cycles:                            4
% 2.62/1.02  pred_elim_time:                         0.005
% 2.62/1.02  splitting_time:                         0.
% 2.62/1.02  sem_filter_time:                        0.
% 2.62/1.02  monotx_time:                            0.001
% 2.62/1.02  subtype_inf_time:                       0.
% 2.62/1.02  
% 2.62/1.02  ------ Problem properties
% 2.62/1.02  
% 2.62/1.02  clauses:                                20
% 2.62/1.02  conjectures:                            4
% 2.62/1.02  epr:                                    0
% 2.62/1.02  horn:                                   16
% 2.62/1.02  ground:                                 7
% 2.62/1.02  unary:                                  6
% 2.62/1.02  binary:                                 5
% 2.62/1.02  lits:                                   49
% 2.62/1.02  lits_eq:                                23
% 2.62/1.02  fd_pure:                                0
% 2.62/1.02  fd_pseudo:                              0
% 2.62/1.02  fd_cond:                                3
% 2.62/1.02  fd_pseudo_cond:                         0
% 2.62/1.02  ac_symbols:                             0
% 2.62/1.02  
% 2.62/1.02  ------ Propositional Solver
% 2.62/1.02  
% 2.62/1.02  prop_solver_calls:                      29
% 2.62/1.02  prop_fast_solver_calls:                 761
% 2.62/1.02  smt_solver_calls:                       0
% 2.62/1.02  smt_fast_solver_calls:                  0
% 2.62/1.02  prop_num_of_clauses:                    973
% 2.62/1.02  prop_preprocess_simplified:             3807
% 2.62/1.02  prop_fo_subsumed:                       18
% 2.62/1.02  prop_solver_time:                       0.
% 2.62/1.02  smt_solver_time:                        0.
% 2.62/1.02  smt_fast_solver_time:                   0.
% 2.62/1.02  prop_fast_solver_time:                  0.
% 2.62/1.02  prop_unsat_core_time:                   0.
% 2.62/1.02  
% 2.62/1.02  ------ QBF
% 2.62/1.02  
% 2.62/1.02  qbf_q_res:                              0
% 2.62/1.02  qbf_num_tautologies:                    0
% 2.62/1.02  qbf_prep_cycles:                        0
% 2.62/1.02  
% 2.62/1.02  ------ BMC1
% 2.62/1.02  
% 2.62/1.02  bmc1_current_bound:                     -1
% 2.62/1.02  bmc1_last_solved_bound:                 -1
% 2.62/1.02  bmc1_unsat_core_size:                   -1
% 2.62/1.02  bmc1_unsat_core_parents_size:           -1
% 2.62/1.02  bmc1_merge_next_fun:                    0
% 2.62/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation
% 2.62/1.02  
% 2.62/1.02  inst_num_of_clauses:                    376
% 2.62/1.02  inst_num_in_passive:                    140
% 2.62/1.02  inst_num_in_active:                     178
% 2.62/1.02  inst_num_in_unprocessed:                58
% 2.62/1.02  inst_num_of_loops:                      200
% 2.62/1.02  inst_num_of_learning_restarts:          0
% 2.62/1.02  inst_num_moves_active_passive:          18
% 2.62/1.02  inst_lit_activity:                      0
% 2.62/1.02  inst_lit_activity_moves:                0
% 2.62/1.02  inst_num_tautologies:                   0
% 2.62/1.02  inst_num_prop_implied:                  0
% 2.62/1.02  inst_num_existing_simplified:           0
% 2.62/1.02  inst_num_eq_res_simplified:             0
% 2.62/1.02  inst_num_child_elim:                    0
% 2.62/1.02  inst_num_of_dismatching_blockings:      48
% 2.62/1.02  inst_num_of_non_proper_insts:           262
% 2.62/1.02  inst_num_of_duplicates:                 0
% 2.62/1.02  inst_inst_num_from_inst_to_res:         0
% 2.62/1.02  inst_dismatching_checking_time:         0.
% 2.62/1.02  
% 2.62/1.02  ------ Resolution
% 2.62/1.02  
% 2.62/1.02  res_num_of_clauses:                     0
% 2.62/1.02  res_num_in_passive:                     0
% 2.62/1.02  res_num_in_active:                      0
% 2.62/1.02  res_num_of_loops:                       120
% 2.62/1.02  res_forward_subset_subsumed:            34
% 2.62/1.02  res_backward_subset_subsumed:           4
% 2.62/1.02  res_forward_subsumed:                   0
% 2.62/1.02  res_backward_subsumed:                  0
% 2.62/1.02  res_forward_subsumption_resolution:     0
% 2.62/1.02  res_backward_subsumption_resolution:    0
% 2.62/1.02  res_clause_to_clause_subsumption:       55
% 2.62/1.02  res_orphan_elimination:                 0
% 2.62/1.02  res_tautology_del:                      30
% 2.62/1.02  res_num_eq_res_simplified:              0
% 2.62/1.02  res_num_sel_changes:                    0
% 2.62/1.02  res_moves_from_active_to_pass:          0
% 2.62/1.02  
% 2.62/1.02  ------ Superposition
% 2.62/1.02  
% 2.62/1.02  sup_time_total:                         0.
% 2.62/1.02  sup_time_generating:                    0.
% 2.62/1.02  sup_time_sim_full:                      0.
% 2.62/1.02  sup_time_sim_immed:                     0.
% 2.62/1.02  
% 2.62/1.02  sup_num_of_clauses:                     27
% 2.62/1.02  sup_num_in_active:                      18
% 2.62/1.02  sup_num_in_passive:                     9
% 2.62/1.02  sup_num_of_loops:                       39
% 2.62/1.02  sup_fw_superposition:                   5
% 2.62/1.02  sup_bw_superposition:                   16
% 2.62/1.02  sup_immediate_simplified:               13
% 2.62/1.02  sup_given_eliminated:                   0
% 2.62/1.02  comparisons_done:                       0
% 2.62/1.02  comparisons_avoided:                    0
% 2.62/1.02  
% 2.62/1.02  ------ Simplifications
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  sim_fw_subset_subsumed:                 9
% 2.62/1.02  sim_bw_subset_subsumed:                 0
% 2.62/1.02  sim_fw_subsumed:                        0
% 2.62/1.02  sim_bw_subsumed:                        0
% 2.62/1.02  sim_fw_subsumption_res:                 0
% 2.62/1.02  sim_bw_subsumption_res:                 0
% 2.62/1.02  sim_tautology_del:                      0
% 2.62/1.02  sim_eq_tautology_del:                   2
% 2.62/1.02  sim_eq_res_simp:                        0
% 2.62/1.02  sim_fw_demodulated:                     0
% 2.62/1.02  sim_bw_demodulated:                     21
% 2.62/1.02  sim_light_normalised:                   12
% 2.62/1.02  sim_joinable_taut:                      0
% 2.62/1.02  sim_joinable_simp:                      0
% 2.62/1.02  sim_ac_normalised:                      0
% 2.62/1.02  sim_smt_subsumption:                    0
% 2.62/1.02  
%------------------------------------------------------------------------------
