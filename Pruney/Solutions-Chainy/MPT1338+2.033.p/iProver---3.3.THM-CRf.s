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
% DateTime   : Thu Dec  3 12:17:06 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  170 (2339 expanded)
%              Number of clauses        :  109 ( 746 expanded)
%              Number of leaves         :   16 ( 660 expanded)
%              Depth                    :   21
%              Number of atoms          :  548 (16028 expanded)
%              Number of equality atoms :  219 (5565 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_967,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1255,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_308,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_309,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_962,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_303,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_304,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_963,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_1283,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1255,c_962,c_963])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1254,plain,
    ( k2_relset_1(X0_55,X1_55,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_1482,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1283,c_1254])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_968,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1280,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_968,c_962,c_963])).

cnf(c_1534,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1482,c_1280])).

cnf(c_1586,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1534,c_1482])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_532,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_533,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_22])).

cnf(c_538,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_956,plain,
    ( ~ v1_funct_2(sK2,X0_55,X1_55)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,sK2) != X1_55 ),
    inference(subtyping,[status(esa)],[c_538])).

cnf(c_1263,plain,
    ( k2_relset_1(X0_55,X1_55,sK2) != X1_55
    | v1_funct_2(sK2,X0_55,X1_55) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_1906,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1263])).

cnf(c_1588,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1534,c_1283])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_966,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1256,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_1277,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1256,c_962,c_963])).

cnf(c_1589,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1534,c_1277])).

cnf(c_2209,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_1588,c_1589])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k1_relset_1(X0_55,X1_55,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1253,plain,
    ( k1_relset_1(X0_55,X1_55,X0_52) = k1_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_2216,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2209,c_1253])).

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

cnf(c_556,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_557,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_22])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_559])).

cnf(c_623,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_954,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_623])).

cnf(c_1265,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_1403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_2077,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_20,c_1403])).

cnf(c_2218,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2216,c_2077])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_461,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_465,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_22])).

cnf(c_466,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_959,plain,
    ( ~ v1_funct_2(sK2,X0_55,X1_55)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,sK2) != X1_55
    | k2_tops_2(X0_55,X1_55,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_1260,plain,
    ( k2_relset_1(X0_55,X1_55,sK2) != X1_55
    | k2_tops_2(X0_55,X1_55,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_55,X1_55) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_1908,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1260])).

cnf(c_2121,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1908,c_1588,c_1589])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_969,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1302,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_969,c_962,c_963])).

cnf(c_1591,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1534,c_1302])).

cnf(c_2124,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2121,c_1591])).

cnf(c_2224,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2218,c_2124])).

cnf(c_2306,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_2224])).

cnf(c_2215,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2209,c_1254])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_570,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_571,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_573,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_22])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_573])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_955,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_611])).

cnf(c_1264,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_2025,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_20,c_1406])).

cnf(c_2221,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2215,c_2025])).

cnf(c_2307,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2306,c_2221])).

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

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_10,c_320])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_10,c_3,c_315])).

cnf(c_406,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_961,plain,
    ( ~ v1_funct_2(X0_52,X0_55,X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_52)
    | k1_relat_1(X0_52) = X0_55
    | k1_xboole_0 = X1_55 ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_1258,plain,
    ( k1_relat_1(X0_52) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_52,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_2012,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1258])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_276,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

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

cnf(c_964,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(c_1271,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_963,c_964])).

cnf(c_1590,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1534,c_1271])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2307,c_2012,c_1590,c_1589,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.12/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.12/0.99  
% 2.12/0.99  ------  iProver source info
% 2.12/0.99  
% 2.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.12/0.99  git: non_committed_changes: false
% 2.12/0.99  git: last_make_outside_of_git: false
% 2.12/0.99  
% 2.12/0.99  ------ 
% 2.12/0.99  
% 2.12/0.99  ------ Input Options
% 2.12/0.99  
% 2.12/0.99  --out_options                           all
% 2.12/0.99  --tptp_safe_out                         true
% 2.12/0.99  --problem_path                          ""
% 2.12/0.99  --include_path                          ""
% 2.12/0.99  --clausifier                            res/vclausify_rel
% 2.12/0.99  --clausifier_options                    --mode clausify
% 2.12/0.99  --stdin                                 false
% 2.12/0.99  --stats_out                             all
% 2.12/0.99  
% 2.12/0.99  ------ General Options
% 2.12/0.99  
% 2.12/0.99  --fof                                   false
% 2.12/0.99  --time_out_real                         305.
% 2.12/0.99  --time_out_virtual                      -1.
% 2.12/0.99  --symbol_type_check                     false
% 2.12/0.99  --clausify_out                          false
% 2.12/0.99  --sig_cnt_out                           false
% 2.12/0.99  --trig_cnt_out                          false
% 2.12/0.99  --trig_cnt_out_tolerance                1.
% 2.12/0.99  --trig_cnt_out_sk_spl                   false
% 2.12/0.99  --abstr_cl_out                          false
% 2.12/0.99  
% 2.12/0.99  ------ Global Options
% 2.12/0.99  
% 2.12/0.99  --schedule                              default
% 2.12/0.99  --add_important_lit                     false
% 2.12/0.99  --prop_solver_per_cl                    1000
% 2.12/0.99  --min_unsat_core                        false
% 2.12/0.99  --soft_assumptions                      false
% 2.12/0.99  --soft_lemma_size                       3
% 2.12/0.99  --prop_impl_unit_size                   0
% 2.12/0.99  --prop_impl_unit                        []
% 2.12/0.99  --share_sel_clauses                     true
% 2.12/0.99  --reset_solvers                         false
% 2.12/0.99  --bc_imp_inh                            [conj_cone]
% 2.12/0.99  --conj_cone_tolerance                   3.
% 2.12/0.99  --extra_neg_conj                        none
% 2.12/0.99  --large_theory_mode                     true
% 2.12/0.99  --prolific_symb_bound                   200
% 2.12/0.99  --lt_threshold                          2000
% 2.12/0.99  --clause_weak_htbl                      true
% 2.12/0.99  --gc_record_bc_elim                     false
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing Options
% 2.12/0.99  
% 2.12/0.99  --preprocessing_flag                    true
% 2.12/0.99  --time_out_prep_mult                    0.1
% 2.12/0.99  --splitting_mode                        input
% 2.12/0.99  --splitting_grd                         true
% 2.12/0.99  --splitting_cvd                         false
% 2.12/0.99  --splitting_cvd_svl                     false
% 2.12/0.99  --splitting_nvd                         32
% 2.12/0.99  --sub_typing                            true
% 2.12/0.99  --prep_gs_sim                           true
% 2.12/0.99  --prep_unflatten                        true
% 2.12/0.99  --prep_res_sim                          true
% 2.12/0.99  --prep_upred                            true
% 2.12/0.99  --prep_sem_filter                       exhaustive
% 2.12/0.99  --prep_sem_filter_out                   false
% 2.12/0.99  --pred_elim                             true
% 2.12/0.99  --res_sim_input                         true
% 2.12/0.99  --eq_ax_congr_red                       true
% 2.12/0.99  --pure_diseq_elim                       true
% 2.12/0.99  --brand_transform                       false
% 2.12/0.99  --non_eq_to_eq                          false
% 2.12/0.99  --prep_def_merge                        true
% 2.12/0.99  --prep_def_merge_prop_impl              false
% 2.12/0.99  --prep_def_merge_mbd                    true
% 2.12/0.99  --prep_def_merge_tr_red                 false
% 2.12/0.99  --prep_def_merge_tr_cl                  false
% 2.12/0.99  --smt_preprocessing                     true
% 2.12/0.99  --smt_ac_axioms                         fast
% 2.12/0.99  --preprocessed_out                      false
% 2.12/0.99  --preprocessed_stats                    false
% 2.12/0.99  
% 2.12/0.99  ------ Abstraction refinement Options
% 2.12/0.99  
% 2.12/0.99  --abstr_ref                             []
% 2.12/0.99  --abstr_ref_prep                        false
% 2.12/0.99  --abstr_ref_until_sat                   false
% 2.12/0.99  --abstr_ref_sig_restrict                funpre
% 2.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/0.99  --abstr_ref_under                       []
% 2.12/0.99  
% 2.12/0.99  ------ SAT Options
% 2.12/0.99  
% 2.12/0.99  --sat_mode                              false
% 2.12/0.99  --sat_fm_restart_options                ""
% 2.12/0.99  --sat_gr_def                            false
% 2.12/0.99  --sat_epr_types                         true
% 2.12/0.99  --sat_non_cyclic_types                  false
% 2.12/0.99  --sat_finite_models                     false
% 2.12/0.99  --sat_fm_lemmas                         false
% 2.12/0.99  --sat_fm_prep                           false
% 2.12/0.99  --sat_fm_uc_incr                        true
% 2.12/0.99  --sat_out_model                         small
% 2.12/0.99  --sat_out_clauses                       false
% 2.12/0.99  
% 2.12/0.99  ------ QBF Options
% 2.12/0.99  
% 2.12/0.99  --qbf_mode                              false
% 2.12/0.99  --qbf_elim_univ                         false
% 2.12/0.99  --qbf_dom_inst                          none
% 2.12/0.99  --qbf_dom_pre_inst                      false
% 2.12/0.99  --qbf_sk_in                             false
% 2.12/0.99  --qbf_pred_elim                         true
% 2.12/0.99  --qbf_split                             512
% 2.12/0.99  
% 2.12/0.99  ------ BMC1 Options
% 2.12/0.99  
% 2.12/0.99  --bmc1_incremental                      false
% 2.12/0.99  --bmc1_axioms                           reachable_all
% 2.12/0.99  --bmc1_min_bound                        0
% 2.12/0.99  --bmc1_max_bound                        -1
% 2.12/0.99  --bmc1_max_bound_default                -1
% 2.12/0.99  --bmc1_symbol_reachability              true
% 2.12/0.99  --bmc1_property_lemmas                  false
% 2.12/0.99  --bmc1_k_induction                      false
% 2.12/0.99  --bmc1_non_equiv_states                 false
% 2.12/0.99  --bmc1_deadlock                         false
% 2.12/0.99  --bmc1_ucm                              false
% 2.12/0.99  --bmc1_add_unsat_core                   none
% 2.12/0.99  --bmc1_unsat_core_children              false
% 2.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/0.99  --bmc1_out_stat                         full
% 2.12/0.99  --bmc1_ground_init                      false
% 2.12/0.99  --bmc1_pre_inst_next_state              false
% 2.12/0.99  --bmc1_pre_inst_state                   false
% 2.12/0.99  --bmc1_pre_inst_reach_state             false
% 2.12/0.99  --bmc1_out_unsat_core                   false
% 2.12/0.99  --bmc1_aig_witness_out                  false
% 2.12/0.99  --bmc1_verbose                          false
% 2.12/0.99  --bmc1_dump_clauses_tptp                false
% 2.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.12/0.99  --bmc1_dump_file                        -
% 2.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.12/0.99  --bmc1_ucm_extend_mode                  1
% 2.12/0.99  --bmc1_ucm_init_mode                    2
% 2.12/0.99  --bmc1_ucm_cone_mode                    none
% 2.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.12/0.99  --bmc1_ucm_relax_model                  4
% 2.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/0.99  --bmc1_ucm_layered_model                none
% 2.12/0.99  --bmc1_ucm_max_lemma_size               10
% 2.12/0.99  
% 2.12/0.99  ------ AIG Options
% 2.12/0.99  
% 2.12/0.99  --aig_mode                              false
% 2.12/0.99  
% 2.12/0.99  ------ Instantiation Options
% 2.12/0.99  
% 2.12/0.99  --instantiation_flag                    true
% 2.12/0.99  --inst_sos_flag                         false
% 2.12/0.99  --inst_sos_phase                        true
% 2.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/0.99  --inst_lit_sel_side                     num_symb
% 2.12/0.99  --inst_solver_per_active                1400
% 2.12/0.99  --inst_solver_calls_frac                1.
% 2.12/0.99  --inst_passive_queue_type               priority_queues
% 2.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/0.99  --inst_passive_queues_freq              [25;2]
% 2.12/0.99  --inst_dismatching                      true
% 2.12/0.99  --inst_eager_unprocessed_to_passive     true
% 2.12/0.99  --inst_prop_sim_given                   true
% 2.12/0.99  --inst_prop_sim_new                     false
% 2.12/0.99  --inst_subs_new                         false
% 2.12/0.99  --inst_eq_res_simp                      false
% 2.12/0.99  --inst_subs_given                       false
% 2.12/0.99  --inst_orphan_elimination               true
% 2.12/0.99  --inst_learning_loop_flag               true
% 2.12/0.99  --inst_learning_start                   3000
% 2.12/0.99  --inst_learning_factor                  2
% 2.12/0.99  --inst_start_prop_sim_after_learn       3
% 2.12/0.99  --inst_sel_renew                        solver
% 2.12/0.99  --inst_lit_activity_flag                true
% 2.12/0.99  --inst_restr_to_given                   false
% 2.12/0.99  --inst_activity_threshold               500
% 2.12/0.99  --inst_out_proof                        true
% 2.12/0.99  
% 2.12/0.99  ------ Resolution Options
% 2.12/0.99  
% 2.12/0.99  --resolution_flag                       true
% 2.12/0.99  --res_lit_sel                           adaptive
% 2.12/0.99  --res_lit_sel_side                      none
% 2.12/0.99  --res_ordering                          kbo
% 2.12/0.99  --res_to_prop_solver                    active
% 2.12/0.99  --res_prop_simpl_new                    false
% 2.12/0.99  --res_prop_simpl_given                  true
% 2.12/0.99  --res_passive_queue_type                priority_queues
% 2.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/0.99  --res_passive_queues_freq               [15;5]
% 2.12/0.99  --res_forward_subs                      full
% 2.12/0.99  --res_backward_subs                     full
% 2.12/0.99  --res_forward_subs_resolution           true
% 2.12/0.99  --res_backward_subs_resolution          true
% 2.12/0.99  --res_orphan_elimination                true
% 2.12/0.99  --res_time_limit                        2.
% 2.12/0.99  --res_out_proof                         true
% 2.12/0.99  
% 2.12/0.99  ------ Superposition Options
% 2.12/0.99  
% 2.12/0.99  --superposition_flag                    true
% 2.12/0.99  --sup_passive_queue_type                priority_queues
% 2.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.12/0.99  --demod_completeness_check              fast
% 2.12/0.99  --demod_use_ground                      true
% 2.12/0.99  --sup_to_prop_solver                    passive
% 2.12/0.99  --sup_prop_simpl_new                    true
% 2.12/0.99  --sup_prop_simpl_given                  true
% 2.12/0.99  --sup_fun_splitting                     false
% 2.12/0.99  --sup_smt_interval                      50000
% 2.12/0.99  
% 2.12/0.99  ------ Superposition Simplification Setup
% 2.12/0.99  
% 2.12/0.99  --sup_indices_passive                   []
% 2.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_full_bw                           [BwDemod]
% 2.12/0.99  --sup_immed_triv                        [TrivRules]
% 2.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_immed_bw_main                     []
% 2.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/0.99  
% 2.12/0.99  ------ Combination Options
% 2.12/0.99  
% 2.12/0.99  --comb_res_mult                         3
% 2.12/0.99  --comb_sup_mult                         2
% 2.12/0.99  --comb_inst_mult                        10
% 2.12/0.99  
% 2.12/0.99  ------ Debug Options
% 2.12/0.99  
% 2.12/0.99  --dbg_backtrace                         false
% 2.12/0.99  --dbg_dump_prop_clauses                 false
% 2.12/0.99  --dbg_dump_prop_clauses_file            -
% 2.12/0.99  --dbg_out_stat                          false
% 2.12/0.99  ------ Parsing...
% 2.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.12/0.99  ------ Proving...
% 2.12/0.99  ------ Problem Properties 
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  clauses                                 18
% 2.12/0.99  conjectures                             5
% 2.12/0.99  EPR                                     1
% 2.12/0.99  Horn                                    17
% 2.12/0.99  unary                                   7
% 2.12/0.99  binary                                  5
% 2.12/0.99  lits                                    43
% 2.12/0.99  lits eq                                 18
% 2.12/0.99  fd_pure                                 0
% 2.12/0.99  fd_pseudo                               0
% 2.12/0.99  fd_cond                                 0
% 2.12/0.99  fd_pseudo_cond                          1
% 2.12/0.99  AC symbols                              0
% 2.12/0.99  
% 2.12/0.99  ------ Schedule dynamic 5 is on 
% 2.12/0.99  
% 2.12/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  ------ 
% 2.12/0.99  Current options:
% 2.12/0.99  ------ 
% 2.12/0.99  
% 2.12/0.99  ------ Input Options
% 2.12/0.99  
% 2.12/0.99  --out_options                           all
% 2.12/0.99  --tptp_safe_out                         true
% 2.12/0.99  --problem_path                          ""
% 2.12/0.99  --include_path                          ""
% 2.12/0.99  --clausifier                            res/vclausify_rel
% 2.12/0.99  --clausifier_options                    --mode clausify
% 2.12/0.99  --stdin                                 false
% 2.12/0.99  --stats_out                             all
% 2.12/0.99  
% 2.12/0.99  ------ General Options
% 2.12/0.99  
% 2.12/0.99  --fof                                   false
% 2.12/0.99  --time_out_real                         305.
% 2.12/0.99  --time_out_virtual                      -1.
% 2.12/0.99  --symbol_type_check                     false
% 2.12/0.99  --clausify_out                          false
% 2.12/0.99  --sig_cnt_out                           false
% 2.12/0.99  --trig_cnt_out                          false
% 2.12/0.99  --trig_cnt_out_tolerance                1.
% 2.12/0.99  --trig_cnt_out_sk_spl                   false
% 2.12/0.99  --abstr_cl_out                          false
% 2.12/0.99  
% 2.12/0.99  ------ Global Options
% 2.12/0.99  
% 2.12/0.99  --schedule                              default
% 2.12/0.99  --add_important_lit                     false
% 2.12/0.99  --prop_solver_per_cl                    1000
% 2.12/0.99  --min_unsat_core                        false
% 2.12/0.99  --soft_assumptions                      false
% 2.12/0.99  --soft_lemma_size                       3
% 2.12/0.99  --prop_impl_unit_size                   0
% 2.12/0.99  --prop_impl_unit                        []
% 2.12/0.99  --share_sel_clauses                     true
% 2.12/0.99  --reset_solvers                         false
% 2.12/0.99  --bc_imp_inh                            [conj_cone]
% 2.12/0.99  --conj_cone_tolerance                   3.
% 2.12/0.99  --extra_neg_conj                        none
% 2.12/0.99  --large_theory_mode                     true
% 2.12/0.99  --prolific_symb_bound                   200
% 2.12/0.99  --lt_threshold                          2000
% 2.12/0.99  --clause_weak_htbl                      true
% 2.12/0.99  --gc_record_bc_elim                     false
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing Options
% 2.12/0.99  
% 2.12/0.99  --preprocessing_flag                    true
% 2.12/0.99  --time_out_prep_mult                    0.1
% 2.12/0.99  --splitting_mode                        input
% 2.12/0.99  --splitting_grd                         true
% 2.12/0.99  --splitting_cvd                         false
% 2.12/0.99  --splitting_cvd_svl                     false
% 2.12/0.99  --splitting_nvd                         32
% 2.12/0.99  --sub_typing                            true
% 2.12/0.99  --prep_gs_sim                           true
% 2.12/0.99  --prep_unflatten                        true
% 2.12/0.99  --prep_res_sim                          true
% 2.12/0.99  --prep_upred                            true
% 2.12/0.99  --prep_sem_filter                       exhaustive
% 2.12/0.99  --prep_sem_filter_out                   false
% 2.12/0.99  --pred_elim                             true
% 2.12/0.99  --res_sim_input                         true
% 2.12/0.99  --eq_ax_congr_red                       true
% 2.12/0.99  --pure_diseq_elim                       true
% 2.12/0.99  --brand_transform                       false
% 2.12/0.99  --non_eq_to_eq                          false
% 2.12/0.99  --prep_def_merge                        true
% 2.12/0.99  --prep_def_merge_prop_impl              false
% 2.12/0.99  --prep_def_merge_mbd                    true
% 2.12/0.99  --prep_def_merge_tr_red                 false
% 2.12/0.99  --prep_def_merge_tr_cl                  false
% 2.12/0.99  --smt_preprocessing                     true
% 2.12/0.99  --smt_ac_axioms                         fast
% 2.12/0.99  --preprocessed_out                      false
% 2.12/0.99  --preprocessed_stats                    false
% 2.12/0.99  
% 2.12/0.99  ------ Abstraction refinement Options
% 2.12/0.99  
% 2.12/0.99  --abstr_ref                             []
% 2.12/0.99  --abstr_ref_prep                        false
% 2.12/0.99  --abstr_ref_until_sat                   false
% 2.12/0.99  --abstr_ref_sig_restrict                funpre
% 2.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/0.99  --abstr_ref_under                       []
% 2.12/0.99  
% 2.12/0.99  ------ SAT Options
% 2.12/0.99  
% 2.12/0.99  --sat_mode                              false
% 2.12/0.99  --sat_fm_restart_options                ""
% 2.12/0.99  --sat_gr_def                            false
% 2.12/0.99  --sat_epr_types                         true
% 2.12/0.99  --sat_non_cyclic_types                  false
% 2.12/0.99  --sat_finite_models                     false
% 2.12/0.99  --sat_fm_lemmas                         false
% 2.12/0.99  --sat_fm_prep                           false
% 2.12/0.99  --sat_fm_uc_incr                        true
% 2.12/0.99  --sat_out_model                         small
% 2.12/0.99  --sat_out_clauses                       false
% 2.12/0.99  
% 2.12/0.99  ------ QBF Options
% 2.12/0.99  
% 2.12/0.99  --qbf_mode                              false
% 2.12/0.99  --qbf_elim_univ                         false
% 2.12/0.99  --qbf_dom_inst                          none
% 2.12/0.99  --qbf_dom_pre_inst                      false
% 2.12/0.99  --qbf_sk_in                             false
% 2.12/0.99  --qbf_pred_elim                         true
% 2.12/0.99  --qbf_split                             512
% 2.12/0.99  
% 2.12/0.99  ------ BMC1 Options
% 2.12/0.99  
% 2.12/0.99  --bmc1_incremental                      false
% 2.12/0.99  --bmc1_axioms                           reachable_all
% 2.12/0.99  --bmc1_min_bound                        0
% 2.12/0.99  --bmc1_max_bound                        -1
% 2.12/0.99  --bmc1_max_bound_default                -1
% 2.12/0.99  --bmc1_symbol_reachability              true
% 2.12/0.99  --bmc1_property_lemmas                  false
% 2.12/0.99  --bmc1_k_induction                      false
% 2.12/0.99  --bmc1_non_equiv_states                 false
% 2.12/0.99  --bmc1_deadlock                         false
% 2.12/0.99  --bmc1_ucm                              false
% 2.12/0.99  --bmc1_add_unsat_core                   none
% 2.12/0.99  --bmc1_unsat_core_children              false
% 2.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/0.99  --bmc1_out_stat                         full
% 2.12/0.99  --bmc1_ground_init                      false
% 2.12/0.99  --bmc1_pre_inst_next_state              false
% 2.12/0.99  --bmc1_pre_inst_state                   false
% 2.12/0.99  --bmc1_pre_inst_reach_state             false
% 2.12/0.99  --bmc1_out_unsat_core                   false
% 2.12/0.99  --bmc1_aig_witness_out                  false
% 2.12/0.99  --bmc1_verbose                          false
% 2.12/0.99  --bmc1_dump_clauses_tptp                false
% 2.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.12/0.99  --bmc1_dump_file                        -
% 2.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.12/0.99  --bmc1_ucm_extend_mode                  1
% 2.12/0.99  --bmc1_ucm_init_mode                    2
% 2.12/0.99  --bmc1_ucm_cone_mode                    none
% 2.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.12/0.99  --bmc1_ucm_relax_model                  4
% 2.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/0.99  --bmc1_ucm_layered_model                none
% 2.12/0.99  --bmc1_ucm_max_lemma_size               10
% 2.12/0.99  
% 2.12/0.99  ------ AIG Options
% 2.12/0.99  
% 2.12/0.99  --aig_mode                              false
% 2.12/0.99  
% 2.12/0.99  ------ Instantiation Options
% 2.12/0.99  
% 2.12/0.99  --instantiation_flag                    true
% 2.12/0.99  --inst_sos_flag                         false
% 2.12/0.99  --inst_sos_phase                        true
% 2.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/0.99  --inst_lit_sel_side                     none
% 2.12/0.99  --inst_solver_per_active                1400
% 2.12/0.99  --inst_solver_calls_frac                1.
% 2.12/0.99  --inst_passive_queue_type               priority_queues
% 2.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/0.99  --inst_passive_queues_freq              [25;2]
% 2.12/0.99  --inst_dismatching                      true
% 2.12/0.99  --inst_eager_unprocessed_to_passive     true
% 2.12/0.99  --inst_prop_sim_given                   true
% 2.12/0.99  --inst_prop_sim_new                     false
% 2.12/0.99  --inst_subs_new                         false
% 2.12/0.99  --inst_eq_res_simp                      false
% 2.12/0.99  --inst_subs_given                       false
% 2.12/0.99  --inst_orphan_elimination               true
% 2.12/0.99  --inst_learning_loop_flag               true
% 2.12/0.99  --inst_learning_start                   3000
% 2.12/0.99  --inst_learning_factor                  2
% 2.12/0.99  --inst_start_prop_sim_after_learn       3
% 2.12/0.99  --inst_sel_renew                        solver
% 2.12/0.99  --inst_lit_activity_flag                true
% 2.12/0.99  --inst_restr_to_given                   false
% 2.12/0.99  --inst_activity_threshold               500
% 2.12/0.99  --inst_out_proof                        true
% 2.12/0.99  
% 2.12/0.99  ------ Resolution Options
% 2.12/0.99  
% 2.12/0.99  --resolution_flag                       false
% 2.12/0.99  --res_lit_sel                           adaptive
% 2.12/0.99  --res_lit_sel_side                      none
% 2.12/0.99  --res_ordering                          kbo
% 2.12/0.99  --res_to_prop_solver                    active
% 2.12/0.99  --res_prop_simpl_new                    false
% 2.12/0.99  --res_prop_simpl_given                  true
% 2.12/0.99  --res_passive_queue_type                priority_queues
% 2.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/0.99  --res_passive_queues_freq               [15;5]
% 2.12/0.99  --res_forward_subs                      full
% 2.12/0.99  --res_backward_subs                     full
% 2.12/0.99  --res_forward_subs_resolution           true
% 2.12/0.99  --res_backward_subs_resolution          true
% 2.12/0.99  --res_orphan_elimination                true
% 2.12/0.99  --res_time_limit                        2.
% 2.12/0.99  --res_out_proof                         true
% 2.12/0.99  
% 2.12/0.99  ------ Superposition Options
% 2.12/0.99  
% 2.12/0.99  --superposition_flag                    true
% 2.12/0.99  --sup_passive_queue_type                priority_queues
% 2.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.12/0.99  --demod_completeness_check              fast
% 2.12/0.99  --demod_use_ground                      true
% 2.12/0.99  --sup_to_prop_solver                    passive
% 2.12/0.99  --sup_prop_simpl_new                    true
% 2.12/0.99  --sup_prop_simpl_given                  true
% 2.12/0.99  --sup_fun_splitting                     false
% 2.12/0.99  --sup_smt_interval                      50000
% 2.12/0.99  
% 2.12/0.99  ------ Superposition Simplification Setup
% 2.12/0.99  
% 2.12/0.99  --sup_indices_passive                   []
% 2.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_full_bw                           [BwDemod]
% 2.12/0.99  --sup_immed_triv                        [TrivRules]
% 2.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_immed_bw_main                     []
% 2.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/0.99  
% 2.12/0.99  ------ Combination Options
% 2.12/0.99  
% 2.12/0.99  --comb_res_mult                         3
% 2.12/0.99  --comb_sup_mult                         2
% 2.12/0.99  --comb_inst_mult                        10
% 2.12/0.99  
% 2.12/0.99  ------ Debug Options
% 2.12/0.99  
% 2.12/0.99  --dbg_backtrace                         false
% 2.12/0.99  --dbg_dump_prop_clauses                 false
% 2.12/0.99  --dbg_dump_prop_clauses_file            -
% 2.12/0.99  --dbg_out_stat                          false
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  ------ Proving...
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  % SZS status Theorem for theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  fof(f13,conjecture,(
% 2.12/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f14,negated_conjecture,(
% 2.12/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.12/0.99    inference(negated_conjecture,[],[f13])).
% 2.12/0.99  
% 2.12/0.99  fof(f33,plain,(
% 2.12/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.12/0.99    inference(ennf_transformation,[],[f14])).
% 2.12/0.99  
% 2.12/0.99  fof(f34,plain,(
% 2.12/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.12/0.99    inference(flattening,[],[f33])).
% 2.12/0.99  
% 2.12/0.99  fof(f38,plain,(
% 2.12/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.12/0.99    introduced(choice_axiom,[])).
% 2.12/0.99  
% 2.12/0.99  fof(f37,plain,(
% 2.12/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.12/0.99    introduced(choice_axiom,[])).
% 2.12/0.99  
% 2.12/0.99  fof(f36,plain,(
% 2.12/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.12/0.99    introduced(choice_axiom,[])).
% 2.12/0.99  
% 2.12/0.99  fof(f39,plain,(
% 2.12/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).
% 2.12/0.99  
% 2.12/0.99  fof(f62,plain,(
% 2.12/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f10,axiom,(
% 2.12/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f28,plain,(
% 2.12/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.12/0.99    inference(ennf_transformation,[],[f10])).
% 2.12/0.99  
% 2.12/0.99  fof(f54,plain,(
% 2.12/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f28])).
% 2.12/0.99  
% 2.12/0.99  fof(f57,plain,(
% 2.12/0.99    l1_struct_0(sK0)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f59,plain,(
% 2.12/0.99    l1_struct_0(sK1)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f6,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f21,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.99    inference(ennf_transformation,[],[f6])).
% 2.12/0.99  
% 2.12/0.99  fof(f46,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f21])).
% 2.12/0.99  
% 2.12/0.99  fof(f63,plain,(
% 2.12/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f9,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f26,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.12/0.99    inference(ennf_transformation,[],[f9])).
% 2.12/0.99  
% 2.12/0.99  fof(f27,plain,(
% 2.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.12/0.99    inference(flattening,[],[f26])).
% 2.12/0.99  
% 2.12/0.99  fof(f53,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f27])).
% 2.12/0.99  
% 2.12/0.99  fof(f64,plain,(
% 2.12/0.99    v2_funct_1(sK2)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f60,plain,(
% 2.12/0.99    v1_funct_1(sK2)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f61,plain,(
% 2.12/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f5,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f20,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.99    inference(ennf_transformation,[],[f5])).
% 2.12/0.99  
% 2.12/0.99  fof(f45,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f20])).
% 2.12/0.99  
% 2.12/0.99  fof(f3,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f18,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.99    inference(ennf_transformation,[],[f3])).
% 2.12/0.99  
% 2.12/0.99  fof(f43,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f18])).
% 2.12/0.99  
% 2.12/0.99  fof(f2,axiom,(
% 2.12/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f16,plain,(
% 2.12/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.12/0.99    inference(ennf_transformation,[],[f2])).
% 2.12/0.99  
% 2.12/0.99  fof(f17,plain,(
% 2.12/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.99    inference(flattening,[],[f16])).
% 2.12/0.99  
% 2.12/0.99  fof(f41,plain,(
% 2.12/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f17])).
% 2.12/0.99  
% 2.12/0.99  fof(f12,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f31,plain,(
% 2.12/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.12/0.99    inference(ennf_transformation,[],[f12])).
% 2.12/0.99  
% 2.12/0.99  fof(f32,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.12/0.99    inference(flattening,[],[f31])).
% 2.12/0.99  
% 2.12/0.99  fof(f56,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f32])).
% 2.12/0.99  
% 2.12/0.99  fof(f65,plain,(
% 2.12/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  fof(f42,plain,(
% 2.12/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f17])).
% 2.12/0.99  
% 2.12/0.99  fof(f8,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f24,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.12/0.99    inference(ennf_transformation,[],[f8])).
% 2.12/0.99  
% 2.12/0.99  fof(f25,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.12/0.99    inference(flattening,[],[f24])).
% 2.12/0.99  
% 2.12/0.99  fof(f49,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f25])).
% 2.12/0.99  
% 2.12/0.99  fof(f4,axiom,(
% 2.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f15,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.12/0.99    inference(pure_predicate_removal,[],[f4])).
% 2.12/0.99  
% 2.12/0.99  fof(f19,plain,(
% 2.12/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.99    inference(ennf_transformation,[],[f15])).
% 2.12/0.99  
% 2.12/0.99  fof(f44,plain,(
% 2.12/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f19])).
% 2.12/0.99  
% 2.12/0.99  fof(f7,axiom,(
% 2.12/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f22,plain,(
% 2.12/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.12/0.99    inference(ennf_transformation,[],[f7])).
% 2.12/0.99  
% 2.12/0.99  fof(f23,plain,(
% 2.12/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.12/0.99    inference(flattening,[],[f22])).
% 2.12/0.99  
% 2.12/0.99  fof(f35,plain,(
% 2.12/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.12/0.99    inference(nnf_transformation,[],[f23])).
% 2.12/0.99  
% 2.12/0.99  fof(f47,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f35])).
% 2.12/0.99  
% 2.12/0.99  fof(f1,axiom,(
% 2.12/0.99    v1_xboole_0(k1_xboole_0)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f40,plain,(
% 2.12/0.99    v1_xboole_0(k1_xboole_0)),
% 2.12/0.99    inference(cnf_transformation,[],[f1])).
% 2.12/0.99  
% 2.12/0.99  fof(f11,axiom,(
% 2.12/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f29,plain,(
% 2.12/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.12/0.99    inference(ennf_transformation,[],[f11])).
% 2.12/0.99  
% 2.12/0.99  fof(f30,plain,(
% 2.12/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.12/0.99    inference(flattening,[],[f29])).
% 2.12/0.99  
% 2.12/0.99  fof(f55,plain,(
% 2.12/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f30])).
% 2.12/0.99  
% 2.12/0.99  fof(f58,plain,(
% 2.12/0.99    ~v2_struct_0(sK1)),
% 2.12/0.99    inference(cnf_transformation,[],[f39])).
% 2.12/0.99  
% 2.12/0.99  cnf(c_20,negated_conjecture,
% 2.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.12/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_967,negated_conjecture,
% 2.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1255,plain,
% 2.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_14,plain,
% 2.12/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_25,negated_conjecture,
% 2.12/0.99      ( l1_struct_0(sK0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_308,plain,
% 2.12/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_309,plain,
% 2.12/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_962,plain,
% 2.12/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_309]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_23,negated_conjecture,
% 2.12/0.99      ( l1_struct_0(sK1) ),
% 2.12/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_303,plain,
% 2.12/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_304,plain,
% 2.12/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_303]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_963,plain,
% 2.12/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_304]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1283,plain,
% 2.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.12/0.99      inference(light_normalisation,[status(thm)],[c_1255,c_962,c_963]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_6,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_970,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/0.99      | k2_relset_1(X0_55,X1_55,X0_52) = k2_relat_1(X0_52) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1254,plain,
% 2.12/0.99      ( k2_relset_1(X0_55,X1_55,X0_52) = k2_relat_1(X0_52)
% 2.12/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1482,plain,
% 2.12/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(superposition,[status(thm)],[c_1283,c_1254]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_19,negated_conjecture,
% 2.12/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.12/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_968,negated_conjecture,
% 2.12/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1280,plain,
% 2.12/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.12/0.99      inference(light_normalisation,[status(thm)],[c_968,c_962,c_963]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1534,plain,
% 2.12/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(demodulation,[status(thm)],[c_1482,c_1280]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1586,plain,
% 2.12/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(demodulation,[status(thm)],[c_1534,c_1482]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_11,plain,
% 2.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | ~ v2_funct_1(X0)
% 2.12/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.12/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_18,negated_conjecture,
% 2.12/0.99      ( v2_funct_1(sK2) ),
% 2.12/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_532,plain,
% 2.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.12/0.99      | sK2 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_533,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | ~ v1_funct_1(sK2)
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_532]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_22,negated_conjecture,
% 2.12/0.99      ( v1_funct_1(sK2) ),
% 2.12/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_537,plain,
% 2.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.12/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(global_propositional_subsumption,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_533,c_22]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_538,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(renaming,[status(thm)],[c_537]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_956,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0_55,X1_55)
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/0.99      | k2_relset_1(X0_55,X1_55,sK2) != X1_55 ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_538]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1263,plain,
% 2.12/0.99      ( k2_relset_1(X0_55,X1_55,sK2) != X1_55
% 2.12/0.99      | v1_funct_2(sK2,X0_55,X1_55) != iProver_top
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 2.12/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1906,plain,
% 2.12/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.12/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.12/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.12/0.99      inference(superposition,[status(thm)],[c_1586,c_1263]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1588,plain,
% 2.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.12/0.99      inference(demodulation,[status(thm)],[c_1534,c_1283]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_21,negated_conjecture,
% 2.12/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.12/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_966,negated_conjecture,
% 2.12/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1256,plain,
% 2.12/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1277,plain,
% 2.12/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.12/0.99      inference(light_normalisation,[status(thm)],[c_1256,c_962,c_963]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1589,plain,
% 2.12/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.12/0.99      inference(demodulation,[status(thm)],[c_1534,c_1277]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2209,plain,
% 2.12/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.12/0.99      inference(global_propositional_subsumption,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_1906,c_1588,c_1589]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_5,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_971,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/0.99      | k1_relset_1(X0_55,X1_55,X0_52) = k1_relat_1(X0_52) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1253,plain,
% 2.12/0.99      ( k1_relset_1(X0_55,X1_55,X0_52) = k1_relat_1(X0_52)
% 2.12/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2216,plain,
% 2.12/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.12/0.99      inference(superposition,[status(thm)],[c_2209,c_1253]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_3,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | v1_relat_1(X0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2,plain,
% 2.12/0.99      ( ~ v1_relat_1(X0)
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | ~ v2_funct_1(X0)
% 2.12/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.12/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_556,plain,
% 2.12/0.99      ( ~ v1_relat_1(X0)
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.12/0.99      | sK2 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_557,plain,
% 2.12/0.99      ( ~ v1_relat_1(sK2)
% 2.12/0.99      | ~ v1_funct_1(sK2)
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_556]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_559,plain,
% 2.12/0.99      ( ~ v1_relat_1(sK2)
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(global_propositional_subsumption,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_557,c_22]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_622,plain,
% 2.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.12/0.99      | sK2 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_559]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_623,plain,
% 2.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_622]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_954,plain,
% 2.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_623]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1265,plain,
% 2.12/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.12/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1403,plain,
% 2.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.12/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_954]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2077,plain,
% 2.12/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(global_propositional_subsumption,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_1265,c_20,c_1403]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2218,plain,
% 2.12/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.12/0.99      inference(light_normalisation,[status(thm)],[c_2216,c_2077]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_16,plain,
% 2.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | ~ v2_funct_1(X0)
% 2.12/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.12/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.12/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_460,plain,
% 2.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/0.99      | ~ v1_funct_1(X0)
% 2.12/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.12/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.12/0.99      | sK2 != X0 ),
% 2.12/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_461,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | ~ v1_funct_1(sK2)
% 2.12/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_465,plain,
% 2.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(global_propositional_subsumption,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_461,c_22]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_466,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.12/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.12/0.99      inference(renaming,[status(thm)],[c_465]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_959,plain,
% 2.12/0.99      ( ~ v1_funct_2(sK2,X0_55,X1_55)
% 2.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/0.99      | k2_relset_1(X0_55,X1_55,sK2) != X1_55
% 2.12/0.99      | k2_tops_2(X0_55,X1_55,sK2) = k2_funct_1(sK2) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_466]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1260,plain,
% 2.12/0.99      ( k2_relset_1(X0_55,X1_55,sK2) != X1_55
% 2.12/0.99      | k2_tops_2(X0_55,X1_55,sK2) = k2_funct_1(sK2)
% 2.12/0.99      | v1_funct_2(sK2,X0_55,X1_55) != iProver_top
% 2.12/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/0.99      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_1908,plain,
% 2.12/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.12/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.12/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.12/1.00      inference(superposition,[status(thm)],[c_1586,c_1260]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2121,plain,
% 2.12/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_1908,c_1588,c_1589]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_17,negated_conjecture,
% 2.12/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.12/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_969,negated_conjecture,
% 2.12/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.12/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1302,plain,
% 2.12/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.12/1.00      inference(light_normalisation,[status(thm)],[c_969,c_962,c_963]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1591,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
% 2.12/1.00      inference(demodulation,[status(thm)],[c_1534,c_1302]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2124,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.12/1.00      inference(demodulation,[status(thm)],[c_2121,c_1591]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2224,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.12/1.00      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.12/1.00      inference(demodulation,[status(thm)],[c_2218,c_2124]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2306,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.12/1.00      inference(equality_resolution_simp,[status(thm)],[c_2224]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2215,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.12/1.00      inference(superposition,[status(thm)],[c_2209,c_1254]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1,plain,
% 2.12/1.00      ( ~ v1_relat_1(X0)
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | ~ v2_funct_1(X0)
% 2.12/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.12/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_570,plain,
% 2.12/1.00      ( ~ v1_relat_1(X0)
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.12/1.00      | sK2 != X0 ),
% 2.12/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_571,plain,
% 2.12/1.00      ( ~ v1_relat_1(sK2)
% 2.12/1.00      | ~ v1_funct_1(sK2)
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_573,plain,
% 2.12/1.00      ( ~ v1_relat_1(sK2)
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_571,c_22]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_610,plain,
% 2.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.12/1.00      | sK2 != X0 ),
% 2.12/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_573]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_611,plain,
% 2.12/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(unflattening,[status(thm)],[c_610]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_955,plain,
% 2.12/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(subtyping,[status(esa)],[c_611]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1264,plain,
% 2.12/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.12/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.12/1.00      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1406,plain,
% 2.12/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.12/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(instantiation,[status(thm)],[c_955]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2025,plain,
% 2.12/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_1264,c_20,c_1406]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2221,plain,
% 2.12/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.12/1.00      inference(light_normalisation,[status(thm)],[c_2215,c_2025]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2307,plain,
% 2.12/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.12/1.00      inference(light_normalisation,[status(thm)],[c_2306,c_2221]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_10,plain,
% 2.12/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.00      | v1_partfun1(X0,X1)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | k1_xboole_0 = X2 ),
% 2.12/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_4,plain,
% 2.12/1.00      ( v4_relat_1(X0,X1)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.12/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_8,plain,
% 2.12/1.00      ( ~ v1_partfun1(X0,X1)
% 2.12/1.00      | ~ v4_relat_1(X0,X1)
% 2.12/1.00      | ~ v1_relat_1(X0)
% 2.12/1.00      | k1_relat_1(X0) = X1 ),
% 2.12/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_315,plain,
% 2.12/1.00      ( ~ v1_partfun1(X0,X1)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ v1_relat_1(X0)
% 2.12/1.00      | k1_relat_1(X0) = X1 ),
% 2.12/1.00      inference(resolution,[status(thm)],[c_4,c_8]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_319,plain,
% 2.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ v1_partfun1(X0,X1)
% 2.12/1.00      | k1_relat_1(X0) = X1 ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_315,c_8,c_4,c_3]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_320,plain,
% 2.12/1.00      ( ~ v1_partfun1(X0,X1)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | k1_relat_1(X0) = X1 ),
% 2.12/1.00      inference(renaming,[status(thm)],[c_319]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_401,plain,
% 2.12/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | k1_relat_1(X0) = X1
% 2.12/1.00      | k1_xboole_0 = X2 ),
% 2.12/1.00      inference(resolution,[status(thm)],[c_10,c_320]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_405,plain,
% 2.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ v1_funct_2(X0,X1,X2)
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | k1_relat_1(X0) = X1
% 2.12/1.00      | k1_xboole_0 = X2 ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_401,c_10,c_3,c_315]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_406,plain,
% 2.12/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.00      | ~ v1_funct_1(X0)
% 2.12/1.00      | k1_relat_1(X0) = X1
% 2.12/1.00      | k1_xboole_0 = X2 ),
% 2.12/1.00      inference(renaming,[status(thm)],[c_405]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_961,plain,
% 2.12/1.00      ( ~ v1_funct_2(X0_52,X0_55,X1_55)
% 2.12/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.12/1.00      | ~ v1_funct_1(X0_52)
% 2.12/1.00      | k1_relat_1(X0_52) = X0_55
% 2.12/1.00      | k1_xboole_0 = X1_55 ),
% 2.12/1.00      inference(subtyping,[status(esa)],[c_406]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1258,plain,
% 2.12/1.00      ( k1_relat_1(X0_52) = X0_55
% 2.12/1.00      | k1_xboole_0 = X1_55
% 2.12/1.00      | v1_funct_2(X0_52,X0_55,X1_55) != iProver_top
% 2.12/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.12/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 2.12/1.00      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_2012,plain,
% 2.12/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.12/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.12/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.12/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.12/1.00      inference(superposition,[status(thm)],[c_1588,c_1258]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_0,plain,
% 2.12/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.12/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_15,plain,
% 2.12/1.00      ( v2_struct_0(X0)
% 2.12/1.00      | ~ l1_struct_0(X0)
% 2.12/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.12/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_276,plain,
% 2.12/1.00      ( v2_struct_0(X0)
% 2.12/1.00      | ~ l1_struct_0(X0)
% 2.12/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.12/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_24,negated_conjecture,
% 2.12/1.00      ( ~ v2_struct_0(sK1) ),
% 2.12/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_294,plain,
% 2.12/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.12/1.00      inference(resolution_lifted,[status(thm)],[c_276,c_24]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_295,plain,
% 2.12/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.12/1.00      inference(unflattening,[status(thm)],[c_294]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_278,plain,
% 2.12/1.00      ( v2_struct_0(sK1)
% 2.12/1.00      | ~ l1_struct_0(sK1)
% 2.12/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.12/1.00      inference(instantiation,[status(thm)],[c_276]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_297,plain,
% 2.12/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.12/1.00      inference(global_propositional_subsumption,
% 2.12/1.00                [status(thm)],
% 2.12/1.00                [c_295,c_24,c_23,c_278]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_964,plain,
% 2.12/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.12/1.00      inference(subtyping,[status(esa)],[c_297]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1271,plain,
% 2.12/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.12/1.00      inference(demodulation,[status(thm)],[c_963,c_964]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_1590,plain,
% 2.12/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.12/1.00      inference(demodulation,[status(thm)],[c_1534,c_1271]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(c_29,plain,
% 2.12/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.12/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.12/1.00  
% 2.12/1.00  cnf(contradiction,plain,
% 2.12/1.00      ( $false ),
% 2.12/1.00      inference(minisat,[status(thm)],[c_2307,c_2012,c_1590,c_1589,c_29]) ).
% 2.12/1.00  
% 2.12/1.00  
% 2.12/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.12/1.00  
% 2.12/1.00  ------                               Statistics
% 2.12/1.00  
% 2.12/1.00  ------ General
% 2.12/1.00  
% 2.12/1.00  abstr_ref_over_cycles:                  0
% 2.12/1.00  abstr_ref_under_cycles:                 0
% 2.12/1.00  gc_basic_clause_elim:                   0
% 2.12/1.00  forced_gc_time:                         0
% 2.12/1.00  parsing_time:                           0.016
% 2.12/1.00  unif_index_cands_time:                  0.
% 2.12/1.00  unif_index_add_time:                    0.
% 2.12/1.00  orderings_time:                         0.
% 2.12/1.00  out_proof_time:                         0.013
% 2.12/1.00  total_time:                             0.119
% 2.12/1.00  num_of_symbols:                         57
% 2.12/1.00  num_of_terms:                           2018
% 2.12/1.00  
% 2.12/1.00  ------ Preprocessing
% 2.12/1.00  
% 2.12/1.00  num_of_splits:                          0
% 2.12/1.00  num_of_split_atoms:                     0
% 2.12/1.00  num_of_reused_defs:                     0
% 2.12/1.00  num_eq_ax_congr_red:                    6
% 2.12/1.00  num_of_sem_filtered_clauses:            1
% 2.12/1.00  num_of_subtypes:                        5
% 2.12/1.00  monotx_restored_types:                  1
% 2.12/1.00  sat_num_of_epr_types:                   0
% 2.12/1.00  sat_num_of_non_cyclic_types:            0
% 2.12/1.00  sat_guarded_non_collapsed_types:        0
% 2.12/1.00  num_pure_diseq_elim:                    0
% 2.12/1.00  simp_replaced_by:                       0
% 2.12/1.00  res_preprocessed:                       115
% 2.12/1.00  prep_upred:                             0
% 2.12/1.00  prep_unflattend:                        25
% 2.12/1.00  smt_new_axioms:                         0
% 2.12/1.00  pred_elim_cands:                        3
% 2.12/1.00  pred_elim:                              7
% 2.12/1.00  pred_elim_cl:                           8
% 2.12/1.00  pred_elim_cycles:                       10
% 2.12/1.00  merged_defs:                            0
% 2.12/1.00  merged_defs_ncl:                        0
% 2.12/1.00  bin_hyper_res:                          0
% 2.12/1.00  prep_cycles:                            4
% 2.12/1.00  pred_elim_time:                         0.012
% 2.12/1.00  splitting_time:                         0.
% 2.12/1.00  sem_filter_time:                        0.
% 2.12/1.00  monotx_time:                            0.001
% 2.12/1.00  subtype_inf_time:                       0.001
% 2.12/1.00  
% 2.12/1.00  ------ Problem properties
% 2.12/1.00  
% 2.12/1.00  clauses:                                18
% 2.12/1.00  conjectures:                            5
% 2.12/1.00  epr:                                    1
% 2.12/1.00  horn:                                   17
% 2.12/1.00  ground:                                 8
% 2.12/1.00  unary:                                  7
% 2.12/1.00  binary:                                 5
% 2.12/1.00  lits:                                   43
% 2.12/1.00  lits_eq:                                18
% 2.12/1.00  fd_pure:                                0
% 2.12/1.00  fd_pseudo:                              0
% 2.12/1.00  fd_cond:                                0
% 2.12/1.00  fd_pseudo_cond:                         1
% 2.12/1.00  ac_symbols:                             0
% 2.12/1.00  
% 2.12/1.00  ------ Propositional Solver
% 2.12/1.00  
% 2.12/1.00  prop_solver_calls:                      28
% 2.12/1.00  prop_fast_solver_calls:                 789
% 2.12/1.00  smt_solver_calls:                       0
% 2.12/1.00  smt_fast_solver_calls:                  0
% 2.12/1.00  prop_num_of_clauses:                    673
% 2.12/1.00  prop_preprocess_simplified:             3135
% 2.12/1.00  prop_fo_subsumed:                       20
% 2.12/1.00  prop_solver_time:                       0.
% 2.12/1.00  smt_solver_time:                        0.
% 2.12/1.00  smt_fast_solver_time:                   0.
% 2.12/1.00  prop_fast_solver_time:                  0.
% 2.12/1.00  prop_unsat_core_time:                   0.
% 2.12/1.00  
% 2.12/1.00  ------ QBF
% 2.12/1.00  
% 2.12/1.00  qbf_q_res:                              0
% 2.12/1.00  qbf_num_tautologies:                    0
% 2.12/1.00  qbf_prep_cycles:                        0
% 2.12/1.00  
% 2.12/1.00  ------ BMC1
% 2.12/1.00  
% 2.12/1.00  bmc1_current_bound:                     -1
% 2.12/1.00  bmc1_last_solved_bound:                 -1
% 2.12/1.00  bmc1_unsat_core_size:                   -1
% 2.12/1.00  bmc1_unsat_core_parents_size:           -1
% 2.12/1.00  bmc1_merge_next_fun:                    0
% 2.12/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.12/1.00  
% 2.12/1.00  ------ Instantiation
% 2.12/1.00  
% 2.12/1.00  inst_num_of_clauses:                    215
% 2.12/1.00  inst_num_in_passive:                    67
% 2.12/1.00  inst_num_in_active:                     144
% 2.12/1.00  inst_num_in_unprocessed:                4
% 2.12/1.00  inst_num_of_loops:                      170
% 2.12/1.00  inst_num_of_learning_restarts:          0
% 2.12/1.00  inst_num_moves_active_passive:          21
% 2.12/1.00  inst_lit_activity:                      0
% 2.12/1.00  inst_lit_activity_moves:                0
% 2.12/1.00  inst_num_tautologies:                   0
% 2.12/1.00  inst_num_prop_implied:                  0
% 2.12/1.00  inst_num_existing_simplified:           0
% 2.12/1.00  inst_num_eq_res_simplified:             0
% 2.12/1.00  inst_num_child_elim:                    0
% 2.12/1.00  inst_num_of_dismatching_blockings:      12
% 2.12/1.00  inst_num_of_non_proper_insts:           198
% 2.12/1.00  inst_num_of_duplicates:                 0
% 2.12/1.00  inst_inst_num_from_inst_to_res:         0
% 2.12/1.00  inst_dismatching_checking_time:         0.
% 2.12/1.00  
% 2.12/1.00  ------ Resolution
% 2.12/1.00  
% 2.12/1.00  res_num_of_clauses:                     0
% 2.12/1.00  res_num_in_passive:                     0
% 2.12/1.00  res_num_in_active:                      0
% 2.12/1.00  res_num_of_loops:                       119
% 2.12/1.00  res_forward_subset_subsumed:            37
% 2.12/1.00  res_backward_subset_subsumed:           0
% 2.12/1.00  res_forward_subsumed:                   0
% 2.12/1.00  res_backward_subsumed:                  0
% 2.12/1.00  res_forward_subsumption_resolution:     1
% 2.12/1.00  res_backward_subsumption_resolution:    0
% 2.12/1.00  res_clause_to_clause_subsumption:       67
% 2.12/1.00  res_orphan_elimination:                 0
% 2.12/1.00  res_tautology_del:                      28
% 2.12/1.00  res_num_eq_res_simplified:              0
% 2.12/1.00  res_num_sel_changes:                    0
% 2.12/1.00  res_moves_from_active_to_pass:          0
% 2.12/1.00  
% 2.12/1.00  ------ Superposition
% 2.12/1.00  
% 2.12/1.00  sup_time_total:                         0.
% 2.12/1.00  sup_time_generating:                    0.
% 2.12/1.00  sup_time_sim_full:                      0.
% 2.12/1.00  sup_time_sim_immed:                     0.
% 2.12/1.00  
% 2.12/1.00  sup_num_of_clauses:                     25
% 2.12/1.00  sup_num_in_active:                      23
% 2.12/1.00  sup_num_in_passive:                     2
% 2.12/1.00  sup_num_of_loops:                       33
% 2.12/1.00  sup_fw_superposition:                   2
% 2.12/1.00  sup_bw_superposition:                   9
% 2.12/1.00  sup_immediate_simplified:               3
% 2.12/1.00  sup_given_eliminated:                   0
% 2.12/1.00  comparisons_done:                       0
% 2.12/1.00  comparisons_avoided:                    0
% 2.12/1.00  
% 2.12/1.00  ------ Simplifications
% 2.12/1.00  
% 2.12/1.00  
% 2.12/1.00  sim_fw_subset_subsumed:                 1
% 2.12/1.00  sim_bw_subset_subsumed:                 0
% 2.12/1.00  sim_fw_subsumed:                        0
% 2.12/1.00  sim_bw_subsumed:                        0
% 2.12/1.00  sim_fw_subsumption_res:                 0
% 2.12/1.00  sim_bw_subsumption_res:                 0
% 2.12/1.00  sim_tautology_del:                      0
% 2.12/1.00  sim_eq_tautology_del:                   0
% 2.12/1.00  sim_eq_res_simp:                        1
% 2.12/1.00  sim_fw_demodulated:                     0
% 2.12/1.00  sim_bw_demodulated:                     11
% 2.12/1.00  sim_light_normalised:                   7
% 2.12/1.00  sim_joinable_taut:                      0
% 2.12/1.00  sim_joinable_simp:                      0
% 2.12/1.00  sim_ac_normalised:                      0
% 2.12/1.00  sim_smt_subsumption:                    0
% 2.12/1.00  
%------------------------------------------------------------------------------
