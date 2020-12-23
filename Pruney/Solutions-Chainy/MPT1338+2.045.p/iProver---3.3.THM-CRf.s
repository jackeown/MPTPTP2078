%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:08 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  141 (1740 expanded)
%              Number of clauses        :   85 ( 466 expanded)
%              Number of leaves         :   15 ( 532 expanded)
%              Depth                    :   19
%              Number of atoms          :  460 (12909 expanded)
%              Number of equality atoms :  213 (4442 expanded)
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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1038,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_325,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_329,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_330,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_1063,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1038,c_325,c_330])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1045,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1449,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1063,c_1045])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1060,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_21,c_325,c_330])).

cnf(c_2164,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1449,c_1060])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_384,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_24])).

cnf(c_389,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_1036,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_479,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_480,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_24])).

cnf(c_1033,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1240,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_24,c_22,c_480,c_1209])).

cnf(c_1563,plain,
    ( k2_tops_2(X0,X1,sK2) = k4_relat_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1036,c_1240])).

cnf(c_1571,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1563])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1037,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1057,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1037,c_325,c_330])).

cnf(c_1579,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_1057,c_1063])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1132,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_19,c_325,c_330])).

cnf(c_1582,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1579,c_1132])).

cnf(c_2171,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2164,c_1582])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_456,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_24])).

cnf(c_461,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_1034,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1316,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1034,c_1240])).

cnf(c_1324,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1316])).

cnf(c_1671,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_1057,c_1063])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1046,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1890,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1671,c_1046])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1367,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1047])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1048,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1686,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1367,c_1048])).

cnf(c_3189,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1890,c_1686,c_2164])).

cnf(c_3316,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_3189])).

cnf(c_1677,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1671,c_1045])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1049,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1685,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1367,c_1049])).

cnf(c_3140,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1677,c_1685,c_2164])).

cnf(c_3318,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3316,c_3140])).

cnf(c_2174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2164,c_1063])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1039,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3130,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2174,c_1039])).

cnf(c_1889,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1063,c_1046])).

cnf(c_2361,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1889,c_2164])).

cnf(c_3135,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3130,c_2361])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_297,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_315,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_26])).

cnf(c_316,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_318,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_25])).

cnf(c_1054,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_318,c_325])).

cnf(c_2176,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2164,c_1054])).

cnf(c_2175,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2164,c_1057])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3318,c_3135,c_2176,c_2175])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:38:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.35/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.98  
% 2.35/0.98  ------  iProver source info
% 2.35/0.98  
% 2.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.98  git: non_committed_changes: false
% 2.35/0.98  git: last_make_outside_of_git: false
% 2.35/0.98  
% 2.35/0.98  ------ 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options
% 2.35/0.98  
% 2.35/0.98  --out_options                           all
% 2.35/0.98  --tptp_safe_out                         true
% 2.35/0.98  --problem_path                          ""
% 2.35/0.98  --include_path                          ""
% 2.35/0.98  --clausifier                            res/vclausify_rel
% 2.35/0.98  --clausifier_options                    --mode clausify
% 2.35/0.98  --stdin                                 false
% 2.35/0.98  --stats_out                             all
% 2.35/0.98  
% 2.35/0.98  ------ General Options
% 2.35/0.98  
% 2.35/0.98  --fof                                   false
% 2.35/0.98  --time_out_real                         305.
% 2.35/0.98  --time_out_virtual                      -1.
% 2.35/0.98  --symbol_type_check                     false
% 2.35/0.98  --clausify_out                          false
% 2.35/0.98  --sig_cnt_out                           false
% 2.35/0.98  --trig_cnt_out                          false
% 2.35/0.98  --trig_cnt_out_tolerance                1.
% 2.35/0.98  --trig_cnt_out_sk_spl                   false
% 2.35/0.98  --abstr_cl_out                          false
% 2.35/0.98  
% 2.35/0.98  ------ Global Options
% 2.35/0.98  
% 2.35/0.98  --schedule                              default
% 2.35/0.98  --add_important_lit                     false
% 2.35/0.98  --prop_solver_per_cl                    1000
% 2.35/0.98  --min_unsat_core                        false
% 2.35/0.98  --soft_assumptions                      false
% 2.35/0.98  --soft_lemma_size                       3
% 2.35/0.98  --prop_impl_unit_size                   0
% 2.35/0.98  --prop_impl_unit                        []
% 2.35/0.98  --share_sel_clauses                     true
% 2.35/0.98  --reset_solvers                         false
% 2.35/0.98  --bc_imp_inh                            [conj_cone]
% 2.35/0.98  --conj_cone_tolerance                   3.
% 2.35/0.98  --extra_neg_conj                        none
% 2.35/0.98  --large_theory_mode                     true
% 2.35/0.98  --prolific_symb_bound                   200
% 2.35/0.98  --lt_threshold                          2000
% 2.35/0.98  --clause_weak_htbl                      true
% 2.35/0.98  --gc_record_bc_elim                     false
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing Options
% 2.35/0.98  
% 2.35/0.98  --preprocessing_flag                    true
% 2.35/0.98  --time_out_prep_mult                    0.1
% 2.35/0.98  --splitting_mode                        input
% 2.35/0.98  --splitting_grd                         true
% 2.35/0.98  --splitting_cvd                         false
% 2.35/0.98  --splitting_cvd_svl                     false
% 2.35/0.98  --splitting_nvd                         32
% 2.35/0.98  --sub_typing                            true
% 2.35/0.98  --prep_gs_sim                           true
% 2.35/0.98  --prep_unflatten                        true
% 2.35/0.98  --prep_res_sim                          true
% 2.35/0.98  --prep_upred                            true
% 2.35/0.98  --prep_sem_filter                       exhaustive
% 2.35/0.98  --prep_sem_filter_out                   false
% 2.35/0.98  --pred_elim                             true
% 2.35/0.98  --res_sim_input                         true
% 2.35/0.98  --eq_ax_congr_red                       true
% 2.35/0.98  --pure_diseq_elim                       true
% 2.35/0.98  --brand_transform                       false
% 2.35/0.98  --non_eq_to_eq                          false
% 2.35/0.98  --prep_def_merge                        true
% 2.35/0.98  --prep_def_merge_prop_impl              false
% 2.35/0.98  --prep_def_merge_mbd                    true
% 2.35/0.98  --prep_def_merge_tr_red                 false
% 2.35/0.98  --prep_def_merge_tr_cl                  false
% 2.35/0.98  --smt_preprocessing                     true
% 2.35/0.98  --smt_ac_axioms                         fast
% 2.35/0.98  --preprocessed_out                      false
% 2.35/0.98  --preprocessed_stats                    false
% 2.35/0.98  
% 2.35/0.98  ------ Abstraction refinement Options
% 2.35/0.98  
% 2.35/0.98  --abstr_ref                             []
% 2.35/0.98  --abstr_ref_prep                        false
% 2.35/0.98  --abstr_ref_until_sat                   false
% 2.35/0.98  --abstr_ref_sig_restrict                funpre
% 2.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.98  --abstr_ref_under                       []
% 2.35/0.98  
% 2.35/0.98  ------ SAT Options
% 2.35/0.98  
% 2.35/0.98  --sat_mode                              false
% 2.35/0.98  --sat_fm_restart_options                ""
% 2.35/0.98  --sat_gr_def                            false
% 2.35/0.98  --sat_epr_types                         true
% 2.35/0.98  --sat_non_cyclic_types                  false
% 2.35/0.98  --sat_finite_models                     false
% 2.35/0.98  --sat_fm_lemmas                         false
% 2.35/0.98  --sat_fm_prep                           false
% 2.35/0.98  --sat_fm_uc_incr                        true
% 2.35/0.98  --sat_out_model                         small
% 2.35/0.98  --sat_out_clauses                       false
% 2.35/0.98  
% 2.35/0.98  ------ QBF Options
% 2.35/0.98  
% 2.35/0.98  --qbf_mode                              false
% 2.35/0.98  --qbf_elim_univ                         false
% 2.35/0.98  --qbf_dom_inst                          none
% 2.35/0.98  --qbf_dom_pre_inst                      false
% 2.35/0.98  --qbf_sk_in                             false
% 2.35/0.98  --qbf_pred_elim                         true
% 2.35/0.98  --qbf_split                             512
% 2.35/0.98  
% 2.35/0.98  ------ BMC1 Options
% 2.35/0.98  
% 2.35/0.98  --bmc1_incremental                      false
% 2.35/0.98  --bmc1_axioms                           reachable_all
% 2.35/0.98  --bmc1_min_bound                        0
% 2.35/0.98  --bmc1_max_bound                        -1
% 2.35/0.98  --bmc1_max_bound_default                -1
% 2.35/0.98  --bmc1_symbol_reachability              true
% 2.35/0.98  --bmc1_property_lemmas                  false
% 2.35/0.98  --bmc1_k_induction                      false
% 2.35/0.98  --bmc1_non_equiv_states                 false
% 2.35/0.98  --bmc1_deadlock                         false
% 2.35/0.98  --bmc1_ucm                              false
% 2.35/0.98  --bmc1_add_unsat_core                   none
% 2.35/0.98  --bmc1_unsat_core_children              false
% 2.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.98  --bmc1_out_stat                         full
% 2.35/0.98  --bmc1_ground_init                      false
% 2.35/0.98  --bmc1_pre_inst_next_state              false
% 2.35/0.98  --bmc1_pre_inst_state                   false
% 2.35/0.98  --bmc1_pre_inst_reach_state             false
% 2.35/0.98  --bmc1_out_unsat_core                   false
% 2.35/0.98  --bmc1_aig_witness_out                  false
% 2.35/0.98  --bmc1_verbose                          false
% 2.35/0.98  --bmc1_dump_clauses_tptp                false
% 2.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.98  --bmc1_dump_file                        -
% 2.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.98  --bmc1_ucm_extend_mode                  1
% 2.35/0.98  --bmc1_ucm_init_mode                    2
% 2.35/0.98  --bmc1_ucm_cone_mode                    none
% 2.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.98  --bmc1_ucm_relax_model                  4
% 2.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.98  --bmc1_ucm_layered_model                none
% 2.35/0.98  --bmc1_ucm_max_lemma_size               10
% 2.35/0.98  
% 2.35/0.98  ------ AIG Options
% 2.35/0.98  
% 2.35/0.98  --aig_mode                              false
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation Options
% 2.35/0.98  
% 2.35/0.98  --instantiation_flag                    true
% 2.35/0.98  --inst_sos_flag                         false
% 2.35/0.98  --inst_sos_phase                        true
% 2.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel_side                     num_symb
% 2.35/0.98  --inst_solver_per_active                1400
% 2.35/0.98  --inst_solver_calls_frac                1.
% 2.35/0.98  --inst_passive_queue_type               priority_queues
% 2.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.98  --inst_passive_queues_freq              [25;2]
% 2.35/0.98  --inst_dismatching                      true
% 2.35/0.98  --inst_eager_unprocessed_to_passive     true
% 2.35/0.98  --inst_prop_sim_given                   true
% 2.35/0.98  --inst_prop_sim_new                     false
% 2.35/0.98  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       true
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  ------ Parsing...
% 2.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.98  ------ Proving...
% 2.35/0.98  ------ Problem Properties 
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  clauses                                 22
% 2.35/0.98  conjectures                             4
% 2.35/0.98  EPR                                     0
% 2.35/0.98  Horn                                    18
% 2.35/0.98  unary                                   6
% 2.35/0.98  binary                                  7
% 2.35/0.98  lits                                    53
% 2.35/0.98  lits eq                                 24
% 2.35/0.98  fd_pure                                 0
% 2.35/0.98  fd_pseudo                               0
% 2.35/0.98  fd_cond                                 3
% 2.35/0.98  fd_pseudo_cond                          0
% 2.35/0.98  AC symbols                              0
% 2.35/0.98  
% 2.35/0.98  ------ Schedule dynamic 5 is on 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ 
% 2.35/0.98  Current options:
% 2.35/0.98  ------ 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options
% 2.35/0.98  
% 2.35/0.98  --out_options                           all
% 2.35/0.98  --tptp_safe_out                         true
% 2.35/0.98  --problem_path                          ""
% 2.35/0.98  --include_path                          ""
% 2.35/0.98  --clausifier                            res/vclausify_rel
% 2.35/0.98  --clausifier_options                    --mode clausify
% 2.35/0.98  --stdin                                 false
% 2.35/0.98  --stats_out                             all
% 2.35/0.98  
% 2.35/0.98  ------ General Options
% 2.35/0.98  
% 2.35/0.98  --fof                                   false
% 2.35/0.98  --time_out_real                         305.
% 2.35/0.98  --time_out_virtual                      -1.
% 2.35/0.98  --symbol_type_check                     false
% 2.35/0.98  --clausify_out                          false
% 2.35/0.98  --sig_cnt_out                           false
% 2.35/0.98  --trig_cnt_out                          false
% 2.35/0.98  --trig_cnt_out_tolerance                1.
% 2.35/0.98  --trig_cnt_out_sk_spl                   false
% 2.35/0.98  --abstr_cl_out                          false
% 2.35/0.98  
% 2.35/0.98  ------ Global Options
% 2.35/0.98  
% 2.35/0.98  --schedule                              default
% 2.35/0.98  --add_important_lit                     false
% 2.35/0.98  --prop_solver_per_cl                    1000
% 2.35/0.98  --min_unsat_core                        false
% 2.35/0.98  --soft_assumptions                      false
% 2.35/0.98  --soft_lemma_size                       3
% 2.35/0.98  --prop_impl_unit_size                   0
% 2.35/0.98  --prop_impl_unit                        []
% 2.35/0.98  --share_sel_clauses                     true
% 2.35/0.98  --reset_solvers                         false
% 2.35/0.98  --bc_imp_inh                            [conj_cone]
% 2.35/0.98  --conj_cone_tolerance                   3.
% 2.35/0.98  --extra_neg_conj                        none
% 2.35/0.98  --large_theory_mode                     true
% 2.35/0.98  --prolific_symb_bound                   200
% 2.35/0.98  --lt_threshold                          2000
% 2.35/0.98  --clause_weak_htbl                      true
% 2.35/0.98  --gc_record_bc_elim                     false
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing Options
% 2.35/0.98  
% 2.35/0.98  --preprocessing_flag                    true
% 2.35/0.98  --time_out_prep_mult                    0.1
% 2.35/0.98  --splitting_mode                        input
% 2.35/0.98  --splitting_grd                         true
% 2.35/0.98  --splitting_cvd                         false
% 2.35/0.98  --splitting_cvd_svl                     false
% 2.35/0.98  --splitting_nvd                         32
% 2.35/0.98  --sub_typing                            true
% 2.35/0.98  --prep_gs_sim                           true
% 2.35/0.98  --prep_unflatten                        true
% 2.35/0.98  --prep_res_sim                          true
% 2.35/0.98  --prep_upred                            true
% 2.35/0.98  --prep_sem_filter                       exhaustive
% 2.35/0.98  --prep_sem_filter_out                   false
% 2.35/0.98  --pred_elim                             true
% 2.35/0.98  --res_sim_input                         true
% 2.35/0.98  --eq_ax_congr_red                       true
% 2.35/0.98  --pure_diseq_elim                       true
% 2.35/0.98  --brand_transform                       false
% 2.35/0.98  --non_eq_to_eq                          false
% 2.35/0.98  --prep_def_merge                        true
% 2.35/0.98  --prep_def_merge_prop_impl              false
% 2.35/0.98  --prep_def_merge_mbd                    true
% 2.35/0.98  --prep_def_merge_tr_red                 false
% 2.35/0.98  --prep_def_merge_tr_cl                  false
% 2.35/0.98  --smt_preprocessing                     true
% 2.35/0.98  --smt_ac_axioms                         fast
% 2.35/0.98  --preprocessed_out                      false
% 2.35/0.98  --preprocessed_stats                    false
% 2.35/0.98  
% 2.35/0.98  ------ Abstraction refinement Options
% 2.35/0.98  
% 2.35/0.98  --abstr_ref                             []
% 2.35/0.98  --abstr_ref_prep                        false
% 2.35/0.98  --abstr_ref_until_sat                   false
% 2.35/0.98  --abstr_ref_sig_restrict                funpre
% 2.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.98  --abstr_ref_under                       []
% 2.35/0.98  
% 2.35/0.98  ------ SAT Options
% 2.35/0.98  
% 2.35/0.98  --sat_mode                              false
% 2.35/0.98  --sat_fm_restart_options                ""
% 2.35/0.98  --sat_gr_def                            false
% 2.35/0.98  --sat_epr_types                         true
% 2.35/0.98  --sat_non_cyclic_types                  false
% 2.35/0.98  --sat_finite_models                     false
% 2.35/0.98  --sat_fm_lemmas                         false
% 2.35/0.98  --sat_fm_prep                           false
% 2.35/0.98  --sat_fm_uc_incr                        true
% 2.35/0.98  --sat_out_model                         small
% 2.35/0.98  --sat_out_clauses                       false
% 2.35/0.98  
% 2.35/0.98  ------ QBF Options
% 2.35/0.98  
% 2.35/0.98  --qbf_mode                              false
% 2.35/0.98  --qbf_elim_univ                         false
% 2.35/0.98  --qbf_dom_inst                          none
% 2.35/0.98  --qbf_dom_pre_inst                      false
% 2.35/0.98  --qbf_sk_in                             false
% 2.35/0.98  --qbf_pred_elim                         true
% 2.35/0.98  --qbf_split                             512
% 2.35/0.98  
% 2.35/0.98  ------ BMC1 Options
% 2.35/0.98  
% 2.35/0.98  --bmc1_incremental                      false
% 2.35/0.98  --bmc1_axioms                           reachable_all
% 2.35/0.98  --bmc1_min_bound                        0
% 2.35/0.98  --bmc1_max_bound                        -1
% 2.35/0.98  --bmc1_max_bound_default                -1
% 2.35/0.98  --bmc1_symbol_reachability              true
% 2.35/0.98  --bmc1_property_lemmas                  false
% 2.35/0.98  --bmc1_k_induction                      false
% 2.35/0.98  --bmc1_non_equiv_states                 false
% 2.35/0.98  --bmc1_deadlock                         false
% 2.35/0.98  --bmc1_ucm                              false
% 2.35/0.98  --bmc1_add_unsat_core                   none
% 2.35/0.98  --bmc1_unsat_core_children              false
% 2.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.98  --bmc1_out_stat                         full
% 2.35/0.98  --bmc1_ground_init                      false
% 2.35/0.98  --bmc1_pre_inst_next_state              false
% 2.35/0.98  --bmc1_pre_inst_state                   false
% 2.35/0.98  --bmc1_pre_inst_reach_state             false
% 2.35/0.98  --bmc1_out_unsat_core                   false
% 2.35/0.98  --bmc1_aig_witness_out                  false
% 2.35/0.98  --bmc1_verbose                          false
% 2.35/0.98  --bmc1_dump_clauses_tptp                false
% 2.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.98  --bmc1_dump_file                        -
% 2.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.98  --bmc1_ucm_extend_mode                  1
% 2.35/0.98  --bmc1_ucm_init_mode                    2
% 2.35/0.98  --bmc1_ucm_cone_mode                    none
% 2.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.98  --bmc1_ucm_relax_model                  4
% 2.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.98  --bmc1_ucm_layered_model                none
% 2.35/0.98  --bmc1_ucm_max_lemma_size               10
% 2.35/0.98  
% 2.35/0.98  ------ AIG Options
% 2.35/0.98  
% 2.35/0.98  --aig_mode                              false
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation Options
% 2.35/0.98  
% 2.35/0.98  --instantiation_flag                    true
% 2.35/0.98  --inst_sos_flag                         false
% 2.35/0.98  --inst_sos_phase                        true
% 2.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel_side                     none
% 2.35/0.98  --inst_solver_per_active                1400
% 2.35/0.98  --inst_solver_calls_frac                1.
% 2.35/0.98  --inst_passive_queue_type               priority_queues
% 2.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.98  --inst_passive_queues_freq              [25;2]
% 2.35/0.98  --inst_dismatching                      true
% 2.35/0.98  --inst_eager_unprocessed_to_passive     true
% 2.35/0.98  --inst_prop_sim_given                   true
% 2.35/0.98  --inst_prop_sim_new                     false
% 2.35/0.98  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       false
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ Proving...
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  % SZS status Theorem for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  fof(f12,conjecture,(
% 2.35/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f13,negated_conjecture,(
% 2.35/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.35/0.98    inference(negated_conjecture,[],[f12])).
% 2.35/0.98  
% 2.35/0.98  fof(f29,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f13])).
% 2.35/0.98  
% 2.35/0.98  fof(f30,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f29])).
% 2.35/0.98  
% 2.35/0.98  fof(f34,plain,(
% 2.35/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f33,plain,(
% 2.35/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f32,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f35,plain,(
% 2.35/0.98    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).
% 2.35/0.98  
% 2.35/0.98  fof(f60,plain,(
% 2.35/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f9,axiom,(
% 2.35/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f24,plain,(
% 2.35/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f9])).
% 2.35/0.98  
% 2.35/0.98  fof(f52,plain,(
% 2.35/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f24])).
% 2.35/0.98  
% 2.35/0.98  fof(f57,plain,(
% 2.35/0.98    l1_struct_0(sK1)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f55,plain,(
% 2.35/0.98    l1_struct_0(sK0)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f6,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f19,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f6])).
% 2.35/0.98  
% 2.35/0.98  fof(f42,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f19])).
% 2.35/0.98  
% 2.35/0.98  fof(f61,plain,(
% 2.35/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f11,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f27,plain,(
% 2.35/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.35/0.98    inference(ennf_transformation,[],[f11])).
% 2.35/0.98  
% 2.35/0.98  fof(f28,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.35/0.98    inference(flattening,[],[f27])).
% 2.35/0.98  
% 2.35/0.98  fof(f54,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f28])).
% 2.35/0.98  
% 2.35/0.98  fof(f62,plain,(
% 2.35/0.98    v2_funct_1(sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f58,plain,(
% 2.35/0.98    v1_funct_1(sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f3,axiom,(
% 2.35/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f15,plain,(
% 2.35/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f3])).
% 2.35/0.98  
% 2.35/0.98  fof(f16,plain,(
% 2.35/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.98    inference(flattening,[],[f15])).
% 2.35/0.98  
% 2.35/0.98  fof(f39,plain,(
% 2.35/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f16])).
% 2.35/0.98  
% 2.35/0.98  fof(f4,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f17,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f4])).
% 2.35/0.98  
% 2.35/0.98  fof(f40,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f17])).
% 2.35/0.98  
% 2.35/0.98  fof(f59,plain,(
% 2.35/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f63,plain,(
% 2.35/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f8,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f22,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.35/0.98    inference(ennf_transformation,[],[f8])).
% 2.35/0.98  
% 2.35/0.98  fof(f23,plain,(
% 2.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.35/0.98    inference(flattening,[],[f22])).
% 2.35/0.98  
% 2.35/0.98  fof(f51,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f23])).
% 2.35/0.98  
% 2.35/0.98  fof(f5,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f18,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f5])).
% 2.35/0.98  
% 2.35/0.98  fof(f41,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f18])).
% 2.35/0.98  
% 2.35/0.98  fof(f2,axiom,(
% 2.35/0.98    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f14,plain,(
% 2.35/0.98    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f2])).
% 2.35/0.98  
% 2.35/0.98  fof(f37,plain,(
% 2.35/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f14])).
% 2.35/0.98  
% 2.35/0.98  fof(f38,plain,(
% 2.35/0.98    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f14])).
% 2.35/0.98  
% 2.35/0.98  fof(f7,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f20,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f7])).
% 2.35/0.98  
% 2.35/0.98  fof(f21,plain,(
% 2.35/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(flattening,[],[f20])).
% 2.35/0.98  
% 2.35/0.98  fof(f31,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(nnf_transformation,[],[f21])).
% 2.35/0.98  
% 2.35/0.98  fof(f43,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f31])).
% 2.35/0.98  
% 2.35/0.98  fof(f1,axiom,(
% 2.35/0.98    v1_xboole_0(k1_xboole_0)),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f36,plain,(
% 2.35/0.98    v1_xboole_0(k1_xboole_0)),
% 2.35/0.98    inference(cnf_transformation,[],[f1])).
% 2.35/0.98  
% 2.35/0.98  fof(f10,axiom,(
% 2.35/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f25,plain,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f10])).
% 2.35/0.98  
% 2.35/0.98  fof(f26,plain,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f25])).
% 2.35/0.98  
% 2.35/0.98  fof(f53,plain,(
% 2.35/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f26])).
% 2.35/0.98  
% 2.35/0.98  fof(f56,plain,(
% 2.35/0.98    ~v2_struct_0(sK1)),
% 2.35/0.98    inference(cnf_transformation,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  cnf(c_22,negated_conjecture,
% 2.35/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.35/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1038,plain,
% 2.35/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_16,plain,
% 2.35/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_25,negated_conjecture,
% 2.35/0.98      ( l1_struct_0(sK1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_324,plain,
% 2.35/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_325,plain,
% 2.35/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_324]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_27,negated_conjecture,
% 2.35/0.98      ( l1_struct_0(sK0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_329,plain,
% 2.35/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_330,plain,
% 2.35/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1063,plain,
% 2.35/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.35/0.98      inference(light_normalisation,[status(thm)],[c_1038,c_325,c_330]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1045,plain,
% 2.35/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.35/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1449,plain,
% 2.35/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1063,c_1045]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_21,negated_conjecture,
% 2.35/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1060,plain,
% 2.35/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.35/0.98      inference(light_normalisation,[status(thm)],[c_21,c_325,c_330]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2164,plain,
% 2.35/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.35/0.98      inference(demodulation,[status(thm)],[c_1449,c_1060]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_18,plain,
% 2.35/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | ~ v1_funct_1(X0)
% 2.35/0.98      | ~ v2_funct_1(X0)
% 2.35/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.35/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.35/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_20,negated_conjecture,
% 2.35/0.98      ( v2_funct_1(sK2) ),
% 2.35/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_383,plain,
% 2.35/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | ~ v1_funct_1(X0)
% 2.35/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.35/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.35/0.98      | sK2 != X0 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_384,plain,
% 2.35/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.98      | ~ v1_funct_1(sK2)
% 2.35/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_383]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_24,negated_conjecture,
% 2.35/0.98      ( v1_funct_1(sK2) ),
% 2.35/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_388,plain,
% 2.35/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_384,c_24]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_389,plain,
% 2.35/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_388]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1036,plain,
% 2.35/0.98      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3,plain,
% 2.35/0.98      ( ~ v1_funct_1(X0)
% 2.35/0.98      | ~ v2_funct_1(X0)
% 2.35/0.98      | ~ v1_relat_1(X0)
% 2.35/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_479,plain,
% 2.35/0.98      ( ~ v1_funct_1(X0)
% 2.35/0.98      | ~ v1_relat_1(X0)
% 2.35/0.98      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.35/0.98      | sK2 != X0 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_480,plain,
% 2.35/0.98      ( ~ v1_funct_1(sK2)
% 2.35/0.98      | ~ v1_relat_1(sK2)
% 2.35/0.98      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_479]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_482,plain,
% 2.35/0.98      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_480,c_24]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1033,plain,
% 2.35/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.35/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1209,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.35/0.99      | v1_relat_1(sK2) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1240,plain,
% 2.35/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1033,c_24,c_22,c_480,c_1209]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1563,plain,
% 2.35/0.99      ( k2_tops_2(X0,X1,sK2) = k4_relat_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1036,c_1240]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1571,plain,
% 2.35/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2)
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1060,c_1563]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_23,negated_conjecture,
% 2.35/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1037,plain,
% 2.35/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1057,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1037,c_325,c_330]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1579,plain,
% 2.35/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1571,c_1057,c_1063]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_19,negated_conjecture,
% 2.35/0.99      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.35/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1132,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.35/0.99      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_19,c_325,c_330]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1582,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
% 2.35/0.99      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_1579,c_1132]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2171,plain,
% 2.35/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
% 2.35/0.99      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2164,c_1582]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_13,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | ~ v2_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_455,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_456,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_460,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_456,c_24]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_461,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_460]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1034,plain,
% 2.35/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1316,plain,
% 2.35/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1034,c_1240]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1324,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.35/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1060,c_1316]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1671,plain,
% 2.35/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1324,c_1057,c_1063]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1046,plain,
% 2.35/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1890,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1671,c_1046]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1047,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.35/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1367,plain,
% 2.35/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1063,c_1047]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2,plain,
% 2.35/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1048,plain,
% 2.35/0.99      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1686,plain,
% 2.35/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1367,c_1048]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3189,plain,
% 2.35/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1890,c_1686,c_2164]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3316,plain,
% 2.35/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2171,c_3189]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1677,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1671,c_1045]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1,plain,
% 2.35/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1049,plain,
% 2.35/0.99      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1685,plain,
% 2.35/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1367,c_1049]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3140,plain,
% 2.35/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1677,c_1685,c_2164]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3318,plain,
% 2.35/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3316,c_3140]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2174,plain,
% 2.35/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2164,c_1063]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_12,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1039,plain,
% 2.35/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.35/0.99      | k1_xboole_0 = X1
% 2.35/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3130,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 2.35/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_2174,c_1039]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1889,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1063,c_1046]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2361,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1889,c_2164]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3135,plain,
% 2.35/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.35/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3130,c_2361]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_0,plain,
% 2.35/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_17,plain,
% 2.35/0.99      ( v2_struct_0(X0)
% 2.35/0.99      | ~ l1_struct_0(X0)
% 2.35/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_297,plain,
% 2.35/0.99      ( v2_struct_0(X0)
% 2.35/0.99      | ~ l1_struct_0(X0)
% 2.35/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_26,negated_conjecture,
% 2.35/0.99      ( ~ v2_struct_0(sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_315,plain,
% 2.35/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_297,c_26]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_316,plain,
% 2.35/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_318,plain,
% 2.35/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_316,c_25]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1054,plain,
% 2.35/0.99      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_318,c_325]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2176,plain,
% 2.35/0.99      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2164,c_1054]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2175,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2164,c_1057]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(contradiction,plain,
% 2.35/0.99      ( $false ),
% 2.35/0.99      inference(minisat,[status(thm)],[c_3318,c_3135,c_2176,c_2175]) ).
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  ------                               Statistics
% 2.35/0.99  
% 2.35/0.99  ------ General
% 2.35/0.99  
% 2.35/0.99  abstr_ref_over_cycles:                  0
% 2.35/0.99  abstr_ref_under_cycles:                 0
% 2.35/0.99  gc_basic_clause_elim:                   0
% 2.35/0.99  forced_gc_time:                         0
% 2.35/0.99  parsing_time:                           0.01
% 2.35/0.99  unif_index_cands_time:                  0.
% 2.35/0.99  unif_index_add_time:                    0.
% 2.35/0.99  orderings_time:                         0.
% 2.35/0.99  out_proof_time:                         0.011
% 2.35/0.99  total_time:                             0.111
% 2.35/0.99  num_of_symbols:                         54
% 2.35/0.99  num_of_terms:                           3152
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing
% 2.35/0.99  
% 2.35/0.99  num_of_splits:                          0
% 2.35/0.99  num_of_split_atoms:                     0
% 2.35/0.99  num_of_reused_defs:                     0
% 2.35/0.99  num_eq_ax_congr_red:                    3
% 2.35/0.99  num_of_sem_filtered_clauses:            1
% 2.35/0.99  num_of_subtypes:                        0
% 2.35/0.99  monotx_restored_types:                  0
% 2.35/0.99  sat_num_of_epr_types:                   0
% 2.35/0.99  sat_num_of_non_cyclic_types:            0
% 2.35/0.99  sat_guarded_non_collapsed_types:        0
% 2.35/0.99  num_pure_diseq_elim:                    0
% 2.35/0.99  simp_replaced_by:                       0
% 2.35/0.99  res_preprocessed:                       127
% 2.35/0.99  prep_upred:                             0
% 2.35/0.99  prep_unflattend:                        10
% 2.35/0.99  smt_new_axioms:                         0
% 2.35/0.99  pred_elim_cands:                        3
% 2.35/0.99  pred_elim:                              5
% 2.35/0.99  pred_elim_cl:                           6
% 2.35/0.99  pred_elim_cycles:                       8
% 2.35/0.99  merged_defs:                            0
% 2.35/0.99  merged_defs_ncl:                        0
% 2.35/0.99  bin_hyper_res:                          0
% 2.35/0.99  prep_cycles:                            4
% 2.35/0.99  pred_elim_time:                         0.006
% 2.35/0.99  splitting_time:                         0.
% 2.35/0.99  sem_filter_time:                        0.
% 2.35/0.99  monotx_time:                            0.
% 2.35/0.99  subtype_inf_time:                       0.
% 2.35/0.99  
% 2.35/0.99  ------ Problem properties
% 2.35/0.99  
% 2.35/0.99  clauses:                                22
% 2.35/0.99  conjectures:                            4
% 2.35/0.99  epr:                                    0
% 2.35/0.99  horn:                                   18
% 2.35/0.99  ground:                                 8
% 2.35/0.99  unary:                                  6
% 2.35/0.99  binary:                                 7
% 2.35/0.99  lits:                                   53
% 2.35/0.99  lits_eq:                                24
% 2.35/0.99  fd_pure:                                0
% 2.35/0.99  fd_pseudo:                              0
% 2.35/0.99  fd_cond:                                3
% 2.35/0.99  fd_pseudo_cond:                         0
% 2.35/0.99  ac_symbols:                             0
% 2.35/0.99  
% 2.35/0.99  ------ Propositional Solver
% 2.35/0.99  
% 2.35/0.99  prop_solver_calls:                      27
% 2.35/0.99  prop_fast_solver_calls:                 824
% 2.35/0.99  smt_solver_calls:                       0
% 2.35/0.99  smt_fast_solver_calls:                  0
% 2.35/0.99  prop_num_of_clauses:                    1084
% 2.35/0.99  prop_preprocess_simplified:             4490
% 2.35/0.99  prop_fo_subsumed:                       14
% 2.35/0.99  prop_solver_time:                       0.
% 2.35/0.99  smt_solver_time:                        0.
% 2.35/0.99  smt_fast_solver_time:                   0.
% 2.35/0.99  prop_fast_solver_time:                  0.
% 2.35/0.99  prop_unsat_core_time:                   0.
% 2.35/0.99  
% 2.35/0.99  ------ QBF
% 2.35/0.99  
% 2.35/0.99  qbf_q_res:                              0
% 2.35/0.99  qbf_num_tautologies:                    0
% 2.35/0.99  qbf_prep_cycles:                        0
% 2.35/0.99  
% 2.35/0.99  ------ BMC1
% 2.35/0.99  
% 2.35/0.99  bmc1_current_bound:                     -1
% 2.35/0.99  bmc1_last_solved_bound:                 -1
% 2.35/0.99  bmc1_unsat_core_size:                   -1
% 2.35/0.99  bmc1_unsat_core_parents_size:           -1
% 2.35/0.99  bmc1_merge_next_fun:                    0
% 2.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation
% 2.35/0.99  
% 2.35/0.99  inst_num_of_clauses:                    442
% 2.35/0.99  inst_num_in_passive:                    114
% 2.35/0.99  inst_num_in_active:                     209
% 2.35/0.99  inst_num_in_unprocessed:                120
% 2.35/0.99  inst_num_of_loops:                      230
% 2.35/0.99  inst_num_of_learning_restarts:          0
% 2.35/0.99  inst_num_moves_active_passive:          18
% 2.35/0.99  inst_lit_activity:                      0
% 2.35/0.99  inst_lit_activity_moves:                0
% 2.35/0.99  inst_num_tautologies:                   0
% 2.35/0.99  inst_num_prop_implied:                  0
% 2.35/0.99  inst_num_existing_simplified:           0
% 2.35/0.99  inst_num_eq_res_simplified:             0
% 2.35/0.99  inst_num_child_elim:                    0
% 2.35/0.99  inst_num_of_dismatching_blockings:      78
% 2.35/0.99  inst_num_of_non_proper_insts:           301
% 2.35/0.99  inst_num_of_duplicates:                 0
% 2.35/0.99  inst_inst_num_from_inst_to_res:         0
% 2.35/0.99  inst_dismatching_checking_time:         0.
% 2.35/0.99  
% 2.35/0.99  ------ Resolution
% 2.35/0.99  
% 2.35/0.99  res_num_of_clauses:                     0
% 2.35/0.99  res_num_in_passive:                     0
% 2.35/0.99  res_num_in_active:                      0
% 2.35/0.99  res_num_of_loops:                       131
% 2.35/0.99  res_forward_subset_subsumed:            37
% 2.35/0.99  res_backward_subset_subsumed:           4
% 2.35/0.99  res_forward_subsumed:                   0
% 2.35/0.99  res_backward_subsumed:                  0
% 2.35/0.99  res_forward_subsumption_resolution:     0
% 2.35/0.99  res_backward_subsumption_resolution:    0
% 2.35/0.99  res_clause_to_clause_subsumption:       58
% 2.35/0.99  res_orphan_elimination:                 0
% 2.35/0.99  res_tautology_del:                      39
% 2.35/0.99  res_num_eq_res_simplified:              0
% 2.35/0.99  res_num_sel_changes:                    0
% 2.35/0.99  res_moves_from_active_to_pass:          0
% 2.35/0.99  
% 2.35/0.99  ------ Superposition
% 2.35/0.99  
% 2.35/0.99  sup_time_total:                         0.
% 2.35/0.99  sup_time_generating:                    0.
% 2.35/0.99  sup_time_sim_full:                      0.
% 2.35/0.99  sup_time_sim_immed:                     0.
% 2.35/0.99  
% 2.35/0.99  sup_num_of_clauses:                     37
% 2.35/0.99  sup_num_in_active:                      33
% 2.35/0.99  sup_num_in_passive:                     4
% 2.35/0.99  sup_num_of_loops:                       44
% 2.35/0.99  sup_fw_superposition:                   10
% 2.35/0.99  sup_bw_superposition:                   21
% 2.35/0.99  sup_immediate_simplified:               12
% 2.35/0.99  sup_given_eliminated:                   0
% 2.35/0.99  comparisons_done:                       0
% 2.35/0.99  comparisons_avoided:                    0
% 2.35/0.99  
% 2.35/0.99  ------ Simplifications
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  sim_fw_subset_subsumed:                 9
% 2.35/0.99  sim_bw_subset_subsumed:                 0
% 2.35/0.99  sim_fw_subsumed:                        0
% 2.35/0.99  sim_bw_subsumed:                        0
% 2.35/0.99  sim_fw_subsumption_res:                 0
% 2.35/0.99  sim_bw_subsumption_res:                 0
% 2.35/0.99  sim_tautology_del:                      0
% 2.35/0.99  sim_eq_tautology_del:                   2
% 2.35/0.99  sim_eq_res_simp:                        0
% 2.35/0.99  sim_fw_demodulated:                     0
% 2.35/0.99  sim_bw_demodulated:                     11
% 2.35/0.99  sim_light_normalised:                   16
% 2.35/0.99  sim_joinable_taut:                      0
% 2.35/0.99  sim_joinable_simp:                      0
% 2.35/0.99  sim_ac_normalised:                      0
% 2.35/0.99  sim_smt_subsumption:                    0
% 2.35/0.99  
%------------------------------------------------------------------------------
