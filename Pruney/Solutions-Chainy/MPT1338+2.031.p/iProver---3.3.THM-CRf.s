%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:05 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  174 (2077 expanded)
%              Number of clauses        :  106 ( 554 expanded)
%              Number of leaves         :   18 ( 630 expanded)
%              Depth                    :   21
%              Number of atoms          :  552 (15369 expanded)
%              Number of equality atoms :  240 (5228 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_348,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_349,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_353,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_354,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1296,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_349,c_354])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1276,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1585,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1296,c_1276])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1291,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_23,c_349,c_354])).

cnf(c_2456,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1585,c_1291])).

cnf(c_2511,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2456,c_1296])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1274,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1277,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2185,plain,
    ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k1_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1277])).

cnf(c_3484,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2511,c_2185])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_611,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_22])).

cnf(c_612,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_614,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_26])).

cnf(c_1262,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1671,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_26,c_24,c_612,c_1445])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_505,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_506,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_26])).

cnf(c_511,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_1267,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1815,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1267])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1270,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1288,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1270,c_349,c_354])).

cnf(c_1818,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_1296,c_1288])).

cnf(c_2510,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2456,c_1818])).

cnf(c_3488,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3484,c_1671,c_2510])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2512,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2456,c_1288])).

cnf(c_3625,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_33,c_2512])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1331,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_21,c_349,c_354])).

cnf(c_1821,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1818,c_1331])).

cnf(c_2509,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2456,c_1821])).

cnf(c_3628,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3625,c_2509])).

cnf(c_5021,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_3628])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_529,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_530,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_26])).

cnf(c_535,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_1266,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_1988,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1266])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_321,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_339,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_28])).

cnf(c_340,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_323,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_342,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_28,c_27,c_323])).

cnf(c_1285,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_342,c_349])).

cnf(c_2350,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1988,c_1296,c_1288,c_1285])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_583,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_584,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_26])).

cnf(c_1264,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1753,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_26,c_24,c_584,c_1445])).

cnf(c_2354,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0(sK0))) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2350,c_1753])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1275,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_10])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_10,c_6,c_5])).

cnf(c_365,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_12,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != X1
    | k6_partfun1(X3) != X0
    | k1_relat_1(X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_12])).

cnf(c_407,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1268,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_2670,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1275,c_1268])).

cnf(c_2730,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2354,c_2670])).

cnf(c_2182,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_1274])).

cnf(c_3630,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2182,c_33,c_1296,c_1288])).

cnf(c_3634,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3630,c_2456])).

cnf(c_3641,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3634,c_1276])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_625,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_626,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_628,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_26])).

cnf(c_1261,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_1518,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_26,c_24,c_626,c_1445])).

cnf(c_3650,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3641,c_1518])).

cnf(c_3834,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2730,c_3650])).

cnf(c_5022,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5021,c_2730,c_3834])).

cnf(c_5023,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5022])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:49:14 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.76/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/0.97  
% 2.76/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.97  
% 2.76/0.97  ------  iProver source info
% 2.76/0.97  
% 2.76/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.97  git: non_committed_changes: false
% 2.76/0.97  git: last_make_outside_of_git: false
% 2.76/0.97  
% 2.76/0.97  ------ 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options
% 2.76/0.97  
% 2.76/0.97  --out_options                           all
% 2.76/0.97  --tptp_safe_out                         true
% 2.76/0.97  --problem_path                          ""
% 2.76/0.97  --include_path                          ""
% 2.76/0.97  --clausifier                            res/vclausify_rel
% 2.76/0.97  --clausifier_options                    --mode clausify
% 2.76/0.97  --stdin                                 false
% 2.76/0.97  --stats_out                             all
% 2.76/0.97  
% 2.76/0.97  ------ General Options
% 2.76/0.97  
% 2.76/0.97  --fof                                   false
% 2.76/0.97  --time_out_real                         305.
% 2.76/0.97  --time_out_virtual                      -1.
% 2.76/0.97  --symbol_type_check                     false
% 2.76/0.97  --clausify_out                          false
% 2.76/0.97  --sig_cnt_out                           false
% 2.76/0.97  --trig_cnt_out                          false
% 2.76/0.97  --trig_cnt_out_tolerance                1.
% 2.76/0.97  --trig_cnt_out_sk_spl                   false
% 2.76/0.97  --abstr_cl_out                          false
% 2.76/0.97  
% 2.76/0.97  ------ Global Options
% 2.76/0.97  
% 2.76/0.97  --schedule                              default
% 2.76/0.97  --add_important_lit                     false
% 2.76/0.97  --prop_solver_per_cl                    1000
% 2.76/0.97  --min_unsat_core                        false
% 2.76/0.97  --soft_assumptions                      false
% 2.76/0.97  --soft_lemma_size                       3
% 2.76/0.97  --prop_impl_unit_size                   0
% 2.76/0.97  --prop_impl_unit                        []
% 2.76/0.97  --share_sel_clauses                     true
% 2.76/0.97  --reset_solvers                         false
% 2.76/0.97  --bc_imp_inh                            [conj_cone]
% 2.76/0.97  --conj_cone_tolerance                   3.
% 2.76/0.97  --extra_neg_conj                        none
% 2.76/0.97  --large_theory_mode                     true
% 2.76/0.97  --prolific_symb_bound                   200
% 2.76/0.97  --lt_threshold                          2000
% 2.76/0.97  --clause_weak_htbl                      true
% 2.76/0.97  --gc_record_bc_elim                     false
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing Options
% 2.76/0.97  
% 2.76/0.97  --preprocessing_flag                    true
% 2.76/0.97  --time_out_prep_mult                    0.1
% 2.76/0.97  --splitting_mode                        input
% 2.76/0.97  --splitting_grd                         true
% 2.76/0.97  --splitting_cvd                         false
% 2.76/0.97  --splitting_cvd_svl                     false
% 2.76/0.97  --splitting_nvd                         32
% 2.76/0.97  --sub_typing                            true
% 2.76/0.97  --prep_gs_sim                           true
% 2.76/0.97  --prep_unflatten                        true
% 2.76/0.97  --prep_res_sim                          true
% 2.76/0.97  --prep_upred                            true
% 2.76/0.97  --prep_sem_filter                       exhaustive
% 2.76/0.97  --prep_sem_filter_out                   false
% 2.76/0.97  --pred_elim                             true
% 2.76/0.97  --res_sim_input                         true
% 2.76/0.97  --eq_ax_congr_red                       true
% 2.76/0.97  --pure_diseq_elim                       true
% 2.76/0.97  --brand_transform                       false
% 2.76/0.97  --non_eq_to_eq                          false
% 2.76/0.97  --prep_def_merge                        true
% 2.76/0.97  --prep_def_merge_prop_impl              false
% 2.76/0.97  --prep_def_merge_mbd                    true
% 2.76/0.97  --prep_def_merge_tr_red                 false
% 2.76/0.97  --prep_def_merge_tr_cl                  false
% 2.76/0.97  --smt_preprocessing                     true
% 2.76/0.97  --smt_ac_axioms                         fast
% 2.76/0.97  --preprocessed_out                      false
% 2.76/0.97  --preprocessed_stats                    false
% 2.76/0.97  
% 2.76/0.97  ------ Abstraction refinement Options
% 2.76/0.97  
% 2.76/0.97  --abstr_ref                             []
% 2.76/0.97  --abstr_ref_prep                        false
% 2.76/0.97  --abstr_ref_until_sat                   false
% 2.76/0.97  --abstr_ref_sig_restrict                funpre
% 2.76/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.97  --abstr_ref_under                       []
% 2.76/0.97  
% 2.76/0.97  ------ SAT Options
% 2.76/0.97  
% 2.76/0.97  --sat_mode                              false
% 2.76/0.97  --sat_fm_restart_options                ""
% 2.76/0.97  --sat_gr_def                            false
% 2.76/0.97  --sat_epr_types                         true
% 2.76/0.97  --sat_non_cyclic_types                  false
% 2.76/0.97  --sat_finite_models                     false
% 2.76/0.97  --sat_fm_lemmas                         false
% 2.76/0.97  --sat_fm_prep                           false
% 2.76/0.97  --sat_fm_uc_incr                        true
% 2.76/0.97  --sat_out_model                         small
% 2.76/0.97  --sat_out_clauses                       false
% 2.76/0.97  
% 2.76/0.97  ------ QBF Options
% 2.76/0.97  
% 2.76/0.97  --qbf_mode                              false
% 2.76/0.97  --qbf_elim_univ                         false
% 2.76/0.97  --qbf_dom_inst                          none
% 2.76/0.97  --qbf_dom_pre_inst                      false
% 2.76/0.97  --qbf_sk_in                             false
% 2.76/0.97  --qbf_pred_elim                         true
% 2.76/0.97  --qbf_split                             512
% 2.76/0.97  
% 2.76/0.97  ------ BMC1 Options
% 2.76/0.97  
% 2.76/0.97  --bmc1_incremental                      false
% 2.76/0.97  --bmc1_axioms                           reachable_all
% 2.76/0.97  --bmc1_min_bound                        0
% 2.76/0.97  --bmc1_max_bound                        -1
% 2.76/0.97  --bmc1_max_bound_default                -1
% 2.76/0.97  --bmc1_symbol_reachability              true
% 2.76/0.97  --bmc1_property_lemmas                  false
% 2.76/0.97  --bmc1_k_induction                      false
% 2.76/0.97  --bmc1_non_equiv_states                 false
% 2.76/0.97  --bmc1_deadlock                         false
% 2.76/0.97  --bmc1_ucm                              false
% 2.76/0.97  --bmc1_add_unsat_core                   none
% 2.76/0.97  --bmc1_unsat_core_children              false
% 2.76/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.97  --bmc1_out_stat                         full
% 2.76/0.97  --bmc1_ground_init                      false
% 2.76/0.97  --bmc1_pre_inst_next_state              false
% 2.76/0.97  --bmc1_pre_inst_state                   false
% 2.76/0.97  --bmc1_pre_inst_reach_state             false
% 2.76/0.97  --bmc1_out_unsat_core                   false
% 2.76/0.97  --bmc1_aig_witness_out                  false
% 2.76/0.97  --bmc1_verbose                          false
% 2.76/0.97  --bmc1_dump_clauses_tptp                false
% 2.76/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.97  --bmc1_dump_file                        -
% 2.76/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.97  --bmc1_ucm_extend_mode                  1
% 2.76/0.97  --bmc1_ucm_init_mode                    2
% 2.76/0.97  --bmc1_ucm_cone_mode                    none
% 2.76/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.97  --bmc1_ucm_relax_model                  4
% 2.76/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.97  --bmc1_ucm_layered_model                none
% 2.76/0.97  --bmc1_ucm_max_lemma_size               10
% 2.76/0.97  
% 2.76/0.97  ------ AIG Options
% 2.76/0.97  
% 2.76/0.97  --aig_mode                              false
% 2.76/0.97  
% 2.76/0.97  ------ Instantiation Options
% 2.76/0.97  
% 2.76/0.97  --instantiation_flag                    true
% 2.76/0.97  --inst_sos_flag                         false
% 2.76/0.97  --inst_sos_phase                        true
% 2.76/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel_side                     num_symb
% 2.76/0.97  --inst_solver_per_active                1400
% 2.76/0.97  --inst_solver_calls_frac                1.
% 2.76/0.97  --inst_passive_queue_type               priority_queues
% 2.76/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.97  --inst_passive_queues_freq              [25;2]
% 2.76/0.97  --inst_dismatching                      true
% 2.76/0.97  --inst_eager_unprocessed_to_passive     true
% 2.76/0.97  --inst_prop_sim_given                   true
% 2.76/0.97  --inst_prop_sim_new                     false
% 2.76/0.97  --inst_subs_new                         false
% 2.76/0.97  --inst_eq_res_simp                      false
% 2.76/0.97  --inst_subs_given                       false
% 2.76/0.97  --inst_orphan_elimination               true
% 2.76/0.97  --inst_learning_loop_flag               true
% 2.76/0.97  --inst_learning_start                   3000
% 2.76/0.97  --inst_learning_factor                  2
% 2.76/0.97  --inst_start_prop_sim_after_learn       3
% 2.76/0.97  --inst_sel_renew                        solver
% 2.76/0.97  --inst_lit_activity_flag                true
% 2.76/0.97  --inst_restr_to_given                   false
% 2.76/0.97  --inst_activity_threshold               500
% 2.76/0.97  --inst_out_proof                        true
% 2.76/0.97  
% 2.76/0.97  ------ Resolution Options
% 2.76/0.97  
% 2.76/0.97  --resolution_flag                       true
% 2.76/0.97  --res_lit_sel                           adaptive
% 2.76/0.97  --res_lit_sel_side                      none
% 2.76/0.97  --res_ordering                          kbo
% 2.76/0.97  --res_to_prop_solver                    active
% 2.76/0.97  --res_prop_simpl_new                    false
% 2.76/0.97  --res_prop_simpl_given                  true
% 2.76/0.97  --res_passive_queue_type                priority_queues
% 2.76/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.97  --res_passive_queues_freq               [15;5]
% 2.76/0.97  --res_forward_subs                      full
% 2.76/0.97  --res_backward_subs                     full
% 2.76/0.97  --res_forward_subs_resolution           true
% 2.76/0.97  --res_backward_subs_resolution          true
% 2.76/0.97  --res_orphan_elimination                true
% 2.76/0.97  --res_time_limit                        2.
% 2.76/0.97  --res_out_proof                         true
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Options
% 2.76/0.97  
% 2.76/0.97  --superposition_flag                    true
% 2.76/0.97  --sup_passive_queue_type                priority_queues
% 2.76/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.97  --demod_completeness_check              fast
% 2.76/0.97  --demod_use_ground                      true
% 2.76/0.97  --sup_to_prop_solver                    passive
% 2.76/0.97  --sup_prop_simpl_new                    true
% 2.76/0.97  --sup_prop_simpl_given                  true
% 2.76/0.97  --sup_fun_splitting                     false
% 2.76/0.97  --sup_smt_interval                      50000
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Simplification Setup
% 2.76/0.97  
% 2.76/0.97  --sup_indices_passive                   []
% 2.76/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_full_bw                           [BwDemod]
% 2.76/0.97  --sup_immed_triv                        [TrivRules]
% 2.76/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_immed_bw_main                     []
% 2.76/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  
% 2.76/0.97  ------ Combination Options
% 2.76/0.97  
% 2.76/0.97  --comb_res_mult                         3
% 2.76/0.97  --comb_sup_mult                         2
% 2.76/0.97  --comb_inst_mult                        10
% 2.76/0.97  
% 2.76/0.97  ------ Debug Options
% 2.76/0.97  
% 2.76/0.97  --dbg_backtrace                         false
% 2.76/0.97  --dbg_dump_prop_clauses                 false
% 2.76/0.97  --dbg_dump_prop_clauses_file            -
% 2.76/0.97  --dbg_out_stat                          false
% 2.76/0.97  ------ Parsing...
% 2.76/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.97  ------ Proving...
% 2.76/0.97  ------ Problem Properties 
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  clauses                                 23
% 2.76/0.97  conjectures                             5
% 2.76/0.97  EPR                                     1
% 2.76/0.97  Horn                                    21
% 2.76/0.97  unary                                   8
% 2.76/0.97  binary                                  9
% 2.76/0.97  lits                                    52
% 2.76/0.97  lits eq                                 21
% 2.76/0.97  fd_pure                                 0
% 2.76/0.97  fd_pseudo                               0
% 2.76/0.97  fd_cond                                 2
% 2.76/0.97  fd_pseudo_cond                          0
% 2.76/0.97  AC symbols                              0
% 2.76/0.97  
% 2.76/0.97  ------ Schedule dynamic 5 is on 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  ------ 
% 2.76/0.97  Current options:
% 2.76/0.97  ------ 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options
% 2.76/0.97  
% 2.76/0.97  --out_options                           all
% 2.76/0.97  --tptp_safe_out                         true
% 2.76/0.97  --problem_path                          ""
% 2.76/0.97  --include_path                          ""
% 2.76/0.97  --clausifier                            res/vclausify_rel
% 2.76/0.97  --clausifier_options                    --mode clausify
% 2.76/0.97  --stdin                                 false
% 2.76/0.97  --stats_out                             all
% 2.76/0.97  
% 2.76/0.97  ------ General Options
% 2.76/0.97  
% 2.76/0.97  --fof                                   false
% 2.76/0.97  --time_out_real                         305.
% 2.76/0.97  --time_out_virtual                      -1.
% 2.76/0.97  --symbol_type_check                     false
% 2.76/0.97  --clausify_out                          false
% 2.76/0.97  --sig_cnt_out                           false
% 2.76/0.97  --trig_cnt_out                          false
% 2.76/0.97  --trig_cnt_out_tolerance                1.
% 2.76/0.97  --trig_cnt_out_sk_spl                   false
% 2.76/0.97  --abstr_cl_out                          false
% 2.76/0.97  
% 2.76/0.97  ------ Global Options
% 2.76/0.97  
% 2.76/0.97  --schedule                              default
% 2.76/0.97  --add_important_lit                     false
% 2.76/0.97  --prop_solver_per_cl                    1000
% 2.76/0.97  --min_unsat_core                        false
% 2.76/0.97  --soft_assumptions                      false
% 2.76/0.97  --soft_lemma_size                       3
% 2.76/0.97  --prop_impl_unit_size                   0
% 2.76/0.97  --prop_impl_unit                        []
% 2.76/0.97  --share_sel_clauses                     true
% 2.76/0.97  --reset_solvers                         false
% 2.76/0.97  --bc_imp_inh                            [conj_cone]
% 2.76/0.97  --conj_cone_tolerance                   3.
% 2.76/0.97  --extra_neg_conj                        none
% 2.76/0.97  --large_theory_mode                     true
% 2.76/0.97  --prolific_symb_bound                   200
% 2.76/0.97  --lt_threshold                          2000
% 2.76/0.97  --clause_weak_htbl                      true
% 2.76/0.97  --gc_record_bc_elim                     false
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing Options
% 2.76/0.97  
% 2.76/0.97  --preprocessing_flag                    true
% 2.76/0.97  --time_out_prep_mult                    0.1
% 2.76/0.97  --splitting_mode                        input
% 2.76/0.97  --splitting_grd                         true
% 2.76/0.97  --splitting_cvd                         false
% 2.76/0.97  --splitting_cvd_svl                     false
% 2.76/0.97  --splitting_nvd                         32
% 2.76/0.97  --sub_typing                            true
% 2.76/0.97  --prep_gs_sim                           true
% 2.76/0.97  --prep_unflatten                        true
% 2.76/0.97  --prep_res_sim                          true
% 2.76/0.97  --prep_upred                            true
% 2.76/0.97  --prep_sem_filter                       exhaustive
% 2.76/0.97  --prep_sem_filter_out                   false
% 2.76/0.97  --pred_elim                             true
% 2.76/0.97  --res_sim_input                         true
% 2.76/0.97  --eq_ax_congr_red                       true
% 2.76/0.97  --pure_diseq_elim                       true
% 2.76/0.97  --brand_transform                       false
% 2.76/0.97  --non_eq_to_eq                          false
% 2.76/0.97  --prep_def_merge                        true
% 2.76/0.97  --prep_def_merge_prop_impl              false
% 2.76/0.97  --prep_def_merge_mbd                    true
% 2.76/0.97  --prep_def_merge_tr_red                 false
% 2.76/0.97  --prep_def_merge_tr_cl                  false
% 2.76/0.97  --smt_preprocessing                     true
% 2.76/0.97  --smt_ac_axioms                         fast
% 2.76/0.97  --preprocessed_out                      false
% 2.76/0.97  --preprocessed_stats                    false
% 2.76/0.97  
% 2.76/0.97  ------ Abstraction refinement Options
% 2.76/0.97  
% 2.76/0.97  --abstr_ref                             []
% 2.76/0.97  --abstr_ref_prep                        false
% 2.76/0.97  --abstr_ref_until_sat                   false
% 2.76/0.97  --abstr_ref_sig_restrict                funpre
% 2.76/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.97  --abstr_ref_under                       []
% 2.76/0.97  
% 2.76/0.97  ------ SAT Options
% 2.76/0.97  
% 2.76/0.97  --sat_mode                              false
% 2.76/0.97  --sat_fm_restart_options                ""
% 2.76/0.97  --sat_gr_def                            false
% 2.76/0.97  --sat_epr_types                         true
% 2.76/0.97  --sat_non_cyclic_types                  false
% 2.76/0.97  --sat_finite_models                     false
% 2.76/0.97  --sat_fm_lemmas                         false
% 2.76/0.97  --sat_fm_prep                           false
% 2.76/0.97  --sat_fm_uc_incr                        true
% 2.76/0.97  --sat_out_model                         small
% 2.76/0.97  --sat_out_clauses                       false
% 2.76/0.97  
% 2.76/0.97  ------ QBF Options
% 2.76/0.97  
% 2.76/0.97  --qbf_mode                              false
% 2.76/0.97  --qbf_elim_univ                         false
% 2.76/0.97  --qbf_dom_inst                          none
% 2.76/0.97  --qbf_dom_pre_inst                      false
% 2.76/0.97  --qbf_sk_in                             false
% 2.76/0.97  --qbf_pred_elim                         true
% 2.76/0.97  --qbf_split                             512
% 2.76/0.97  
% 2.76/0.97  ------ BMC1 Options
% 2.76/0.97  
% 2.76/0.97  --bmc1_incremental                      false
% 2.76/0.97  --bmc1_axioms                           reachable_all
% 2.76/0.97  --bmc1_min_bound                        0
% 2.76/0.97  --bmc1_max_bound                        -1
% 2.76/0.97  --bmc1_max_bound_default                -1
% 2.76/0.97  --bmc1_symbol_reachability              true
% 2.76/0.97  --bmc1_property_lemmas                  false
% 2.76/0.97  --bmc1_k_induction                      false
% 2.76/0.97  --bmc1_non_equiv_states                 false
% 2.76/0.97  --bmc1_deadlock                         false
% 2.76/0.97  --bmc1_ucm                              false
% 2.76/0.97  --bmc1_add_unsat_core                   none
% 2.76/0.97  --bmc1_unsat_core_children              false
% 2.76/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.97  --bmc1_out_stat                         full
% 2.76/0.97  --bmc1_ground_init                      false
% 2.76/0.97  --bmc1_pre_inst_next_state              false
% 2.76/0.97  --bmc1_pre_inst_state                   false
% 2.76/0.97  --bmc1_pre_inst_reach_state             false
% 2.76/0.97  --bmc1_out_unsat_core                   false
% 2.76/0.97  --bmc1_aig_witness_out                  false
% 2.76/0.97  --bmc1_verbose                          false
% 2.76/0.97  --bmc1_dump_clauses_tptp                false
% 2.76/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.97  --bmc1_dump_file                        -
% 2.76/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.97  --bmc1_ucm_extend_mode                  1
% 2.76/0.97  --bmc1_ucm_init_mode                    2
% 2.76/0.97  --bmc1_ucm_cone_mode                    none
% 2.76/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.97  --bmc1_ucm_relax_model                  4
% 2.76/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.97  --bmc1_ucm_layered_model                none
% 2.76/0.97  --bmc1_ucm_max_lemma_size               10
% 2.76/0.97  
% 2.76/0.97  ------ AIG Options
% 2.76/0.97  
% 2.76/0.97  --aig_mode                              false
% 2.76/0.97  
% 2.76/0.97  ------ Instantiation Options
% 2.76/0.97  
% 2.76/0.97  --instantiation_flag                    true
% 2.76/0.97  --inst_sos_flag                         false
% 2.76/0.97  --inst_sos_phase                        true
% 2.76/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel_side                     none
% 2.76/0.97  --inst_solver_per_active                1400
% 2.76/0.97  --inst_solver_calls_frac                1.
% 2.76/0.97  --inst_passive_queue_type               priority_queues
% 2.76/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.97  --inst_passive_queues_freq              [25;2]
% 2.76/0.97  --inst_dismatching                      true
% 2.76/0.97  --inst_eager_unprocessed_to_passive     true
% 2.76/0.97  --inst_prop_sim_given                   true
% 2.76/0.97  --inst_prop_sim_new                     false
% 2.76/0.97  --inst_subs_new                         false
% 2.76/0.97  --inst_eq_res_simp                      false
% 2.76/0.97  --inst_subs_given                       false
% 2.76/0.97  --inst_orphan_elimination               true
% 2.76/0.97  --inst_learning_loop_flag               true
% 2.76/0.97  --inst_learning_start                   3000
% 2.76/0.97  --inst_learning_factor                  2
% 2.76/0.97  --inst_start_prop_sim_after_learn       3
% 2.76/0.97  --inst_sel_renew                        solver
% 2.76/0.97  --inst_lit_activity_flag                true
% 2.76/0.97  --inst_restr_to_given                   false
% 2.76/0.97  --inst_activity_threshold               500
% 2.76/0.97  --inst_out_proof                        true
% 2.76/0.97  
% 2.76/0.97  ------ Resolution Options
% 2.76/0.97  
% 2.76/0.97  --resolution_flag                       false
% 2.76/0.97  --res_lit_sel                           adaptive
% 2.76/0.97  --res_lit_sel_side                      none
% 2.76/0.97  --res_ordering                          kbo
% 2.76/0.97  --res_to_prop_solver                    active
% 2.76/0.97  --res_prop_simpl_new                    false
% 2.76/0.97  --res_prop_simpl_given                  true
% 2.76/0.97  --res_passive_queue_type                priority_queues
% 2.76/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.97  --res_passive_queues_freq               [15;5]
% 2.76/0.97  --res_forward_subs                      full
% 2.76/0.97  --res_backward_subs                     full
% 2.76/0.97  --res_forward_subs_resolution           true
% 2.76/0.97  --res_backward_subs_resolution          true
% 2.76/0.97  --res_orphan_elimination                true
% 2.76/0.97  --res_time_limit                        2.
% 2.76/0.97  --res_out_proof                         true
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Options
% 2.76/0.97  
% 2.76/0.97  --superposition_flag                    true
% 2.76/0.97  --sup_passive_queue_type                priority_queues
% 2.76/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.97  --demod_completeness_check              fast
% 2.76/0.97  --demod_use_ground                      true
% 2.76/0.97  --sup_to_prop_solver                    passive
% 2.76/0.97  --sup_prop_simpl_new                    true
% 2.76/0.97  --sup_prop_simpl_given                  true
% 2.76/0.97  --sup_fun_splitting                     false
% 2.76/0.97  --sup_smt_interval                      50000
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Simplification Setup
% 2.76/0.97  
% 2.76/0.97  --sup_indices_passive                   []
% 2.76/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_full_bw                           [BwDemod]
% 2.76/0.97  --sup_immed_triv                        [TrivRules]
% 2.76/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_immed_bw_main                     []
% 2.76/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  
% 2.76/0.97  ------ Combination Options
% 2.76/0.97  
% 2.76/0.97  --comb_res_mult                         3
% 2.76/0.97  --comb_sup_mult                         2
% 2.76/0.97  --comb_inst_mult                        10
% 2.76/0.97  
% 2.76/0.97  ------ Debug Options
% 2.76/0.97  
% 2.76/0.97  --dbg_backtrace                         false
% 2.76/0.97  --dbg_dump_prop_clauses                 false
% 2.76/0.97  --dbg_dump_prop_clauses_file            -
% 2.76/0.97  --dbg_out_stat                          false
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  ------ Proving...
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  % SZS status Theorem for theBenchmark.p
% 2.76/0.97  
% 2.76/0.97   Resolution empty clause
% 2.76/0.97  
% 2.76/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.97  
% 2.76/0.97  fof(f15,conjecture,(
% 2.76/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f16,negated_conjecture,(
% 2.76/0.97    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.76/0.97    inference(negated_conjecture,[],[f15])).
% 2.76/0.97  
% 2.76/0.97  fof(f37,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.76/0.97    inference(ennf_transformation,[],[f16])).
% 2.76/0.97  
% 2.76/0.97  fof(f38,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.76/0.97    inference(flattening,[],[f37])).
% 2.76/0.97  
% 2.76/0.97  fof(f42,plain,(
% 2.76/0.97    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f41,plain,(
% 2.76/0.97    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f40,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f43,plain,(
% 2.76/0.97    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).
% 2.76/0.97  
% 2.76/0.97  fof(f70,plain,(
% 2.76/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.76/0.97    inference(cnf_transformation,[],[f43])).
% 2.76/0.97  
% 2.76/0.97  fof(f11,axiom,(
% 2.76/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f30,plain,(
% 2.76/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.76/0.97    inference(ennf_transformation,[],[f11])).
% 2.76/0.97  
% 2.76/0.97  fof(f59,plain,(
% 2.76/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f30])).
% 2.76/0.97  
% 2.76/0.97  fof(f67,plain,(
% 2.76/0.97    l1_struct_0(sK1)),
% 2.76/0.97    inference(cnf_transformation,[],[f43])).
% 2.76/0.97  
% 2.76/0.97  fof(f65,plain,(
% 2.76/0.97    l1_struct_0(sK0)),
% 2.76/0.97    inference(cnf_transformation,[],[f43])).
% 2.76/0.97  
% 2.76/0.97  fof(f7,axiom,(
% 2.76/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f25,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f7])).
% 2.76/0.98  
% 2.76/0.98  fof(f52,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f25])).
% 2.76/0.98  
% 2.76/0.98  fof(f71,plain,(
% 2.76/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f14,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f35,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.76/0.98    inference(ennf_transformation,[],[f14])).
% 2.76/0.98  
% 2.76/0.98  fof(f36,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/0.98    inference(flattening,[],[f35])).
% 2.76/0.98  
% 2.76/0.98  fof(f64,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f36])).
% 2.76/0.98  
% 2.76/0.98  fof(f6,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f24,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f6])).
% 2.76/0.98  
% 2.76/0.98  fof(f51,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f24])).
% 2.76/0.98  
% 2.76/0.98  fof(f2,axiom,(
% 2.76/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f18,plain,(
% 2.76/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f2])).
% 2.76/0.98  
% 2.76/0.98  fof(f19,plain,(
% 2.76/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.98    inference(flattening,[],[f18])).
% 2.76/0.98  
% 2.76/0.98  fof(f45,plain,(
% 2.76/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f19])).
% 2.76/0.98  
% 2.76/0.98  fof(f72,plain,(
% 2.76/0.98    v2_funct_1(sK2)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f68,plain,(
% 2.76/0.98    v1_funct_1(sK2)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f4,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f22,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f4])).
% 2.76/0.98  
% 2.76/0.98  fof(f49,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f22])).
% 2.76/0.98  
% 2.76/0.98  fof(f13,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f33,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.76/0.98    inference(ennf_transformation,[],[f13])).
% 2.76/0.98  
% 2.76/0.98  fof(f34,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/0.98    inference(flattening,[],[f33])).
% 2.76/0.98  
% 2.76/0.98  fof(f61,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f34])).
% 2.76/0.98  
% 2.76/0.98  fof(f69,plain,(
% 2.76/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f73,plain,(
% 2.76/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f10,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f28,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.76/0.98    inference(ennf_transformation,[],[f10])).
% 2.76/0.98  
% 2.76/0.98  fof(f29,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/0.98    inference(flattening,[],[f28])).
% 2.76/0.98  
% 2.76/0.98  fof(f57,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f29])).
% 2.76/0.98  
% 2.76/0.98  fof(f1,axiom,(
% 2.76/0.98    v1_xboole_0(k1_xboole_0)),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f44,plain,(
% 2.76/0.98    v1_xboole_0(k1_xboole_0)),
% 2.76/0.98    inference(cnf_transformation,[],[f1])).
% 2.76/0.98  
% 2.76/0.98  fof(f12,axiom,(
% 2.76/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f31,plain,(
% 2.76/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f12])).
% 2.76/0.98  
% 2.76/0.98  fof(f32,plain,(
% 2.76/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.76/0.98    inference(flattening,[],[f31])).
% 2.76/0.98  
% 2.76/0.98  fof(f60,plain,(
% 2.76/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f32])).
% 2.76/0.98  
% 2.76/0.98  fof(f66,plain,(
% 2.76/0.98    ~v2_struct_0(sK1)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f3,axiom,(
% 2.76/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f20,plain,(
% 2.76/0.98    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f3])).
% 2.76/0.98  
% 2.76/0.98  fof(f21,plain,(
% 2.76/0.98    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.98    inference(flattening,[],[f20])).
% 2.76/0.98  
% 2.76/0.98  fof(f47,plain,(
% 2.76/0.98    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f21])).
% 2.76/0.98  
% 2.76/0.98  fof(f9,axiom,(
% 2.76/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f56,plain,(
% 2.76/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f9])).
% 2.76/0.98  
% 2.76/0.98  fof(f5,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f17,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.76/0.98    inference(pure_predicate_removal,[],[f5])).
% 2.76/0.98  
% 2.76/0.98  fof(f23,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f17])).
% 2.76/0.98  
% 2.76/0.98  fof(f50,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f23])).
% 2.76/0.98  
% 2.76/0.98  fof(f8,axiom,(
% 2.76/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f26,plain,(
% 2.76/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.76/0.98    inference(ennf_transformation,[],[f8])).
% 2.76/0.98  
% 2.76/0.98  fof(f27,plain,(
% 2.76/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/0.98    inference(flattening,[],[f26])).
% 2.76/0.98  
% 2.76/0.98  fof(f39,plain,(
% 2.76/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/0.98    inference(nnf_transformation,[],[f27])).
% 2.76/0.98  
% 2.76/0.98  fof(f53,plain,(
% 2.76/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f39])).
% 2.76/0.98  
% 2.76/0.98  fof(f55,plain,(
% 2.76/0.98    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f9])).
% 2.76/0.98  
% 2.76/0.98  fof(f46,plain,(
% 2.76/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f19])).
% 2.76/0.98  
% 2.76/0.98  cnf(c_24,negated_conjecture,
% 2.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1271,plain,
% 2.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_15,plain,
% 2.76/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_27,negated_conjecture,
% 2.76/0.98      ( l1_struct_0(sK1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_348,plain,
% 2.76/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_349,plain,
% 2.76/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_348]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_29,negated_conjecture,
% 2.76/0.98      ( l1_struct_0(sK0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_353,plain,
% 2.76/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_354,plain,
% 2.76/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_353]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1296,plain,
% 2.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_1271,c_349,c_354]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_8,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1276,plain,
% 2.76/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1585,plain,
% 2.76/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1296,c_1276]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_23,negated_conjecture,
% 2.76/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1291,plain,
% 2.76/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_23,c_349,c_354]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2456,plain,
% 2.76/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_1585,c_1291]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2511,plain,
% 2.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2456,c_1296]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_18,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.76/0.98      | ~ v1_funct_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1274,plain,
% 2.76/0.98      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.76/0.98      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 2.76/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_7,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1277,plain,
% 2.76/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2185,plain,
% 2.76/0.98      ( k1_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k1_relat_1(k2_tops_2(X1,X0,X2))
% 2.76/0.98      | v1_funct_2(X2,X1,X0) != iProver_top
% 2.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.76/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1274,c_1277]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3484,plain,
% 2.76/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
% 2.76/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.76/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2511,c_2185]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v2_funct_1(X0)
% 2.76/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_22,negated_conjecture,
% 2.76/0.98      ( v2_funct_1(sK2) ),
% 2.76/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_611,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.76/0.98      | sK2 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_22]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_612,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2)
% 2.76/0.98      | ~ v1_funct_1(sK2)
% 2.76/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_611]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_26,negated_conjecture,
% 2.76/0.98      ( v1_funct_1(sK2) ),
% 2.76/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_614,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_612,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1262,plain,
% 2.76/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.76/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_5,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1445,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.76/0.98      | v1_relat_1(sK2) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1671,plain,
% 2.76/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_1262,c_26,c_24,c_612,c_1445]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_17,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v2_funct_1(X0)
% 2.76/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.76/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.76/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_505,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.76/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.76/0.98      | sK2 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_506,plain,
% 2.76/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | ~ v1_funct_1(sK2)
% 2.76/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_505]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_510,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_506,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_511,plain,
% 2.76/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/0.98      inference(renaming,[status(thm)],[c_510]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1267,plain,
% 2.76/0.98      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.76/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1815,plain,
% 2.76/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.76/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1291,c_1267]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_25,negated_conjecture,
% 2.76/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.76/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1270,plain,
% 2.76/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1288,plain,
% 2.76/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_1270,c_349,c_354]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1818,plain,
% 2.76/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_1815,c_1296,c_1288]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2510,plain,
% 2.76/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2456,c_1818]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3488,plain,
% 2.76/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.76/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.76/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_3484,c_1671,c_2510]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_33,plain,
% 2.76/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2512,plain,
% 2.76/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2456,c_1288]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3625,plain,
% 2.76/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_3488,c_33,c_2512]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_21,negated_conjecture,
% 2.76/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.76/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1331,plain,
% 2.76/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.76/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_21,c_349,c_354]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1821,plain,
% 2.76/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.76/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_1818,c_1331]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2509,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.76/0.98      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2456,c_1821]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3628,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.76/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_3625,c_2509]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_5021,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.76/0.98      inference(equality_resolution_simp,[status(thm)],[c_3628]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_14,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v2_funct_1(X0)
% 2.76/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.76/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.76/0.98      | k1_xboole_0 = X2 ),
% 2.76/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_529,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.76/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.76/0.98      | sK2 != X0
% 2.76/0.98      | k1_xboole_0 = X2 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_530,plain,
% 2.76/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | ~ v1_funct_1(sK2)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.76/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.76/0.98      | k1_xboole_0 = X1 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_529]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_534,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.76/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.76/0.98      | k1_xboole_0 = X1 ),
% 2.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_530,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_535,plain,
% 2.76/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.76/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.76/0.98      | k1_xboole_0 = X1 ),
% 2.76/0.98      inference(renaming,[status(thm)],[c_534]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1266,plain,
% 2.76/0.98      ( k2_relset_1(X0,X1,sK2) != X1
% 2.76/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.76/0.98      | k1_xboole_0 = X1
% 2.76/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1988,plain,
% 2.76/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 2.76/0.98      | k2_struct_0(sK1) = k1_xboole_0
% 2.76/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1291,c_1266]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_0,plain,
% 2.76/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_16,plain,
% 2.76/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.76/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_321,plain,
% 2.76/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_28,negated_conjecture,
% 2.76/0.98      ( ~ v2_struct_0(sK1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_339,plain,
% 2.76/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_321,c_28]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_340,plain,
% 2.76/0.98      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_339]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_323,plain,
% 2.76/0.98      ( v2_struct_0(sK1)
% 2.76/0.98      | ~ l1_struct_0(sK1)
% 2.76/0.98      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_321]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_342,plain,
% 2.76/0.98      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_340,c_28,c_27,c_323]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1285,plain,
% 2.76/0.98      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_342,c_349]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2350,plain,
% 2.76/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_1988,c_1296,c_1288,c_1285]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v2_funct_1(X0)
% 2.76/0.98      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_583,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 2.76/0.98      | sK2 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_584,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2)
% 2.76/0.98      | ~ v1_funct_1(sK2)
% 2.76/0.98      | k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_583]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_586,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2)
% 2.76/0.98      | k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_584,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1264,plain,
% 2.76/0.98      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 2.76/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1753,plain,
% 2.76/0.98      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_1264,c_26,c_24,c_584,c_1445]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2354,plain,
% 2.76/0.98      ( k1_relat_1(k6_partfun1(k2_struct_0(sK0))) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2350,c_1753]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_11,plain,
% 2.76/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1275,plain,
% 2.76/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_6,plain,
% 2.76/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_10,plain,
% 2.76/0.98      ( ~ v1_partfun1(X0,X1)
% 2.76/0.98      | ~ v4_relat_1(X0,X1)
% 2.76/0.98      | ~ v1_relat_1(X0)
% 2.76/0.98      | k1_relat_1(X0) = X1 ),
% 2.76/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_360,plain,
% 2.76/0.98      ( ~ v1_partfun1(X0,X1)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_relat_1(X0)
% 2.76/0.98      | k1_relat_1(X0) = X1 ),
% 2.76/0.98      inference(resolution,[status(thm)],[c_6,c_10]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_364,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_partfun1(X0,X1)
% 2.76/0.98      | k1_relat_1(X0) = X1 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_360,c_10,c_6,c_5]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_365,plain,
% 2.76/0.98      ( ~ v1_partfun1(X0,X1)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relat_1(X0) = X1 ),
% 2.76/0.98      inference(renaming,[status(thm)],[c_364]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_12,plain,
% 2.76/0.98      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_406,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | X3 != X1
% 2.76/0.98      | k6_partfun1(X3) != X0
% 2.76/0.98      | k1_relat_1(X0) = X1 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_365,c_12]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_407,plain,
% 2.76/0.98      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.98      | k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_406]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1268,plain,
% 2.76/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0
% 2.76/0.98      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2670,plain,
% 2.76/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1275,c_1268]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2730,plain,
% 2.76/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2354,c_2670]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2182,plain,
% 2.76/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.76/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.76/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_1818,c_1274]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3630,plain,
% 2.76/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_2182,c_33,c_1296,c_1288]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3634,plain,
% 2.76/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_3630,c_2456]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3641,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_3634,c_1276]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v2_funct_1(X0)
% 2.76/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_625,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.76/0.98      | sK2 != X0 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_626,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2)
% 2.76/0.98      | ~ v1_funct_1(sK2)
% 2.76/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_625]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_628,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_626,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1261,plain,
% 2.76/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.76/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1518,plain,
% 2.76/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_1261,c_26,c_24,c_626,c_1445]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3650,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_3641,c_1518]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3834,plain,
% 2.76/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_2730,c_3650]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_5022,plain,
% 2.76/0.98      ( k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.76/0.98      inference(light_normalisation,[status(thm)],[c_5021,c_2730,c_3834]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_5023,plain,
% 2.76/0.98      ( $false ),
% 2.76/0.98      inference(equality_resolution_simp,[status(thm)],[c_5022]) ).
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  ------                               Statistics
% 2.76/0.98  
% 2.76/0.98  ------ General
% 2.76/0.98  
% 2.76/0.98  abstr_ref_over_cycles:                  0
% 2.76/0.98  abstr_ref_under_cycles:                 0
% 2.76/0.98  gc_basic_clause_elim:                   0
% 2.76/0.98  forced_gc_time:                         0
% 2.76/0.98  parsing_time:                           0.01
% 2.76/0.98  unif_index_cands_time:                  0.
% 2.76/0.98  unif_index_add_time:                    0.
% 2.76/0.98  orderings_time:                         0.
% 2.76/0.98  out_proof_time:                         0.009
% 2.76/0.98  total_time:                             0.187
% 2.76/0.98  num_of_symbols:                         57
% 2.76/0.98  num_of_terms:                           4451
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing
% 2.76/0.98  
% 2.76/0.98  num_of_splits:                          0
% 2.76/0.98  num_of_split_atoms:                     0
% 2.76/0.98  num_of_reused_defs:                     0
% 2.76/0.98  num_eq_ax_congr_red:                    6
% 2.76/0.98  num_of_sem_filtered_clauses:            1
% 2.76/0.98  num_of_subtypes:                        0
% 2.76/0.98  monotx_restored_types:                  0
% 2.76/0.98  sat_num_of_epr_types:                   0
% 2.76/0.98  sat_num_of_non_cyclic_types:            0
% 2.76/0.98  sat_guarded_non_collapsed_types:        0
% 2.76/0.98  num_pure_diseq_elim:                    0
% 2.76/0.98  simp_replaced_by:                       0
% 2.76/0.98  res_preprocessed:                       134
% 2.76/0.98  prep_upred:                             0
% 2.76/0.98  prep_unflattend:                        24
% 2.76/0.98  smt_new_axioms:                         0
% 2.76/0.98  pred_elim_cands:                        4
% 2.76/0.98  pred_elim:                              6
% 2.76/0.98  pred_elim_cl:                           7
% 2.76/0.98  pred_elim_cycles:                       9
% 2.76/0.98  merged_defs:                            0
% 2.76/0.98  merged_defs_ncl:                        0
% 2.76/0.98  bin_hyper_res:                          0
% 2.76/0.98  prep_cycles:                            4
% 2.76/0.98  pred_elim_time:                         0.007
% 2.76/0.98  splitting_time:                         0.
% 2.76/0.98  sem_filter_time:                        0.
% 2.76/0.98  monotx_time:                            0.
% 2.76/0.98  subtype_inf_time:                       0.
% 2.76/0.98  
% 2.76/0.98  ------ Problem properties
% 2.76/0.98  
% 2.76/0.98  clauses:                                23
% 2.76/0.98  conjectures:                            5
% 2.76/0.98  epr:                                    1
% 2.76/0.98  horn:                                   21
% 2.76/0.98  ground:                                 12
% 2.76/0.98  unary:                                  8
% 2.76/0.98  binary:                                 9
% 2.76/0.98  lits:                                   52
% 2.76/0.98  lits_eq:                                21
% 2.76/0.98  fd_pure:                                0
% 2.76/0.98  fd_pseudo:                              0
% 2.76/0.98  fd_cond:                                2
% 2.76/0.98  fd_pseudo_cond:                         0
% 2.76/0.98  ac_symbols:                             0
% 2.76/0.98  
% 2.76/0.98  ------ Propositional Solver
% 2.76/0.98  
% 2.76/0.98  prop_solver_calls:                      29
% 2.76/0.98  prop_fast_solver_calls:                 986
% 2.76/0.98  smt_solver_calls:                       0
% 2.76/0.98  smt_fast_solver_calls:                  0
% 2.76/0.98  prop_num_of_clauses:                    1908
% 2.76/0.98  prop_preprocess_simplified:             5175
% 2.76/0.98  prop_fo_subsumed:                       40
% 2.76/0.98  prop_solver_time:                       0.
% 2.76/0.98  smt_solver_time:                        0.
% 2.76/0.98  smt_fast_solver_time:                   0.
% 2.76/0.98  prop_fast_solver_time:                  0.
% 2.76/0.98  prop_unsat_core_time:                   0.
% 2.76/0.98  
% 2.76/0.98  ------ QBF
% 2.76/0.98  
% 2.76/0.98  qbf_q_res:                              0
% 2.76/0.98  qbf_num_tautologies:                    0
% 2.76/0.98  qbf_prep_cycles:                        0
% 2.76/0.98  
% 2.76/0.98  ------ BMC1
% 2.76/0.98  
% 2.76/0.98  bmc1_current_bound:                     -1
% 2.76/0.98  bmc1_last_solved_bound:                 -1
% 2.76/0.98  bmc1_unsat_core_size:                   -1
% 2.76/0.98  bmc1_unsat_core_parents_size:           -1
% 2.76/0.98  bmc1_merge_next_fun:                    0
% 2.76/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.76/0.98  
% 2.76/0.98  ------ Instantiation
% 2.76/0.98  
% 2.76/0.98  inst_num_of_clauses:                    655
% 2.76/0.98  inst_num_in_passive:                    259
% 2.76/0.98  inst_num_in_active:                     374
% 2.76/0.98  inst_num_in_unprocessed:                22
% 2.76/0.98  inst_num_of_loops:                      400
% 2.76/0.98  inst_num_of_learning_restarts:          0
% 2.76/0.98  inst_num_moves_active_passive:          21
% 2.76/0.98  inst_lit_activity:                      0
% 2.76/0.98  inst_lit_activity_moves:                0
% 2.76/0.98  inst_num_tautologies:                   0
% 2.76/0.98  inst_num_prop_implied:                  0
% 2.76/0.98  inst_num_existing_simplified:           0
% 2.76/0.98  inst_num_eq_res_simplified:             0
% 2.76/0.98  inst_num_child_elim:                    0
% 2.76/0.98  inst_num_of_dismatching_blockings:      114
% 2.76/0.98  inst_num_of_non_proper_insts:           547
% 2.76/0.98  inst_num_of_duplicates:                 0
% 2.76/0.98  inst_inst_num_from_inst_to_res:         0
% 2.76/0.98  inst_dismatching_checking_time:         0.
% 2.76/0.98  
% 2.76/0.98  ------ Resolution
% 2.76/0.98  
% 2.76/0.98  res_num_of_clauses:                     0
% 2.76/0.98  res_num_in_passive:                     0
% 2.76/0.98  res_num_in_active:                      0
% 2.76/0.98  res_num_of_loops:                       138
% 2.76/0.98  res_forward_subset_subsumed:            76
% 2.76/0.98  res_backward_subset_subsumed:           2
% 2.76/0.98  res_forward_subsumed:                   0
% 2.76/0.98  res_backward_subsumed:                  0
% 2.76/0.98  res_forward_subsumption_resolution:     1
% 2.76/0.98  res_backward_subsumption_resolution:    0
% 2.76/0.98  res_clause_to_clause_subsumption:       183
% 2.76/0.98  res_orphan_elimination:                 0
% 2.76/0.98  res_tautology_del:                      83
% 2.76/0.98  res_num_eq_res_simplified:              0
% 2.76/0.98  res_num_sel_changes:                    0
% 2.76/0.98  res_moves_from_active_to_pass:          0
% 2.76/0.98  
% 2.76/0.98  ------ Superposition
% 2.76/0.98  
% 2.76/0.98  sup_time_total:                         0.
% 2.76/0.98  sup_time_generating:                    0.
% 2.76/0.98  sup_time_sim_full:                      0.
% 2.76/0.98  sup_time_sim_immed:                     0.
% 2.76/0.98  
% 2.76/0.98  sup_num_of_clauses:                     63
% 2.76/0.98  sup_num_in_active:                      48
% 2.76/0.98  sup_num_in_passive:                     15
% 2.76/0.98  sup_num_of_loops:                       78
% 2.76/0.98  sup_fw_superposition:                   28
% 2.76/0.98  sup_bw_superposition:                   40
% 2.76/0.98  sup_immediate_simplified:               22
% 2.76/0.98  sup_given_eliminated:                   0
% 2.76/0.98  comparisons_done:                       0
% 2.76/0.98  comparisons_avoided:                    0
% 2.76/0.98  
% 2.76/0.98  ------ Simplifications
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  sim_fw_subset_subsumed:                 7
% 2.76/0.98  sim_bw_subset_subsumed:                 3
% 2.76/0.98  sim_fw_subsumed:                        3
% 2.76/0.98  sim_bw_subsumed:                        0
% 2.76/0.98  sim_fw_subsumption_res:                 2
% 2.76/0.98  sim_bw_subsumption_res:                 0
% 2.76/0.98  sim_tautology_del:                      0
% 2.76/0.98  sim_eq_tautology_del:                   6
% 2.76/0.98  sim_eq_res_simp:                        1
% 2.76/0.98  sim_fw_demodulated:                     0
% 2.76/0.98  sim_bw_demodulated:                     29
% 2.76/0.98  sim_light_normalised:                   25
% 2.76/0.98  sim_joinable_taut:                      0
% 2.76/0.98  sim_joinable_simp:                      0
% 2.76/0.98  sim_ac_normalised:                      0
% 2.76/0.98  sim_smt_subsumption:                    0
% 2.76/0.98  
%------------------------------------------------------------------------------
