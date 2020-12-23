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
% DateTime   : Thu Dec  3 12:17:38 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  221 (6945 expanded)
%              Number of clauses        :  142 (2237 expanded)
%              Number of leaves         :   21 (1955 expanded)
%              Depth                    :   23
%              Number of atoms          :  816 (43571 expanded)
%              Number of equality atoms :  312 (7641 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f51,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f50,f49,f48])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f85,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_666,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_383,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_384,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_662,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_378,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_379,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_663,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_1168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1143,c_662,c_663])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1137,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_1574,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1168,c_1137])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_667,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1165,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_667,c_662,c_663])).

cnf(c_1576,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1574,c_1165])).

cnf(c_1622,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1576,c_1574])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1141,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2458,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1622,c_1141])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1624,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1576,c_1168])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_665,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1144,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_1162,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1144,c_662,c_663])).

cnf(c_1625,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1576,c_1162])).

cnf(c_2800,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2458,c_37,c_40,c_1624,c_1625])).

cnf(c_17,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_488,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_660,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1147,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1307,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1147,c_662,c_663])).

cnf(c_1623,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1576,c_1307])).

cnf(c_2803,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2800,c_1623])).

cnf(c_38,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_670,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53))
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1432,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1433,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1432])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1374,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1555,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1555])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_683,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1577,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_1578,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_690,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1491,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_54
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_54 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_1582,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_671,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1139,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2449,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1622,c_1139])).

cnf(c_664,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1145,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_678,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1132,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1845,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1132])).

cnf(c_736,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2020,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1845,c_30,c_28,c_26,c_736,c_1555,c_1577])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_679,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v2_funct_1(X0_53)
    | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1131,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v2_funct_1(X1_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_2257,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2020,c_1131])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_672,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1445,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1446,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_1647,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1651,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_2362,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_2363,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2362])).

cnf(c_2597,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2257,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1446,c_1582,c_1651,c_2363])).

cnf(c_2598,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2597])).

cnf(c_2609,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2598])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_676,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1134,plain,
    ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_1926,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1134])).

cnf(c_742,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_2091,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_30,c_28,c_26,c_742,c_1555,c_1577])).

cnf(c_2614,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2609,c_2091])).

cnf(c_2621,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_37,c_39,c_1556,c_1578])).

cnf(c_2622,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2621])).

cnf(c_2,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_682,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1128,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_2627,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2622,c_1128])).

cnf(c_1138,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_2812,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1622,c_1138])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_365,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_366,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_46,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_368,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_32,c_31,c_46])).

cnf(c_390,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_368])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_391,c_16])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_452,c_11])).

cnf(c_661,plain,
    ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X0_54 ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_1146,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2845,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1146,c_1576])).

cnf(c_2854,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_2845])).

cnf(c_2857,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_37,c_40,c_1624,c_1625])).

cnf(c_2862,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2857,c_1137])).

cnf(c_2869,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2862,c_2020])).

cnf(c_2955,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_1141])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_674,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1136,plain,
    ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1838,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1136])).

cnf(c_748,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2016,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1838,c_30,c_28,c_26,c_748,c_1555,c_1577])).

cnf(c_2978,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2955,c_2016])).

cnf(c_3444,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2803,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1556,c_1578,c_1582,c_1624,c_1625,c_2449,c_2627,c_2812,c_2854,c_2978])).

cnf(c_3066,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2854,c_37,c_39,c_1556,c_1578,c_1625])).

cnf(c_3062,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2978,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1556,c_1578,c_1582,c_1624,c_1625,c_2449,c_2627,c_2812,c_2854])).

cnf(c_3069,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3066,c_3062])).

cnf(c_3448,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3444,c_3066,c_3069])).

cnf(c_3074,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3066,c_1624])).

cnf(c_3076,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3066,c_1625])).

cnf(c_3452,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3448,c_1145,c_3074,c_3076])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.61/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.00  
% 2.61/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/1.00  
% 2.61/1.00  ------  iProver source info
% 2.61/1.00  
% 2.61/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.61/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/1.00  git: non_committed_changes: false
% 2.61/1.00  git: last_make_outside_of_git: false
% 2.61/1.00  
% 2.61/1.00  ------ 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options
% 2.61/1.00  
% 2.61/1.00  --out_options                           all
% 2.61/1.00  --tptp_safe_out                         true
% 2.61/1.00  --problem_path                          ""
% 2.61/1.00  --include_path                          ""
% 2.61/1.00  --clausifier                            res/vclausify_rel
% 2.61/1.00  --clausifier_options                    --mode clausify
% 2.61/1.00  --stdin                                 false
% 2.61/1.00  --stats_out                             all
% 2.61/1.00  
% 2.61/1.00  ------ General Options
% 2.61/1.00  
% 2.61/1.00  --fof                                   false
% 2.61/1.00  --time_out_real                         305.
% 2.61/1.00  --time_out_virtual                      -1.
% 2.61/1.00  --symbol_type_check                     false
% 2.61/1.00  --clausify_out                          false
% 2.61/1.00  --sig_cnt_out                           false
% 2.61/1.00  --trig_cnt_out                          false
% 2.61/1.00  --trig_cnt_out_tolerance                1.
% 2.61/1.00  --trig_cnt_out_sk_spl                   false
% 2.61/1.00  --abstr_cl_out                          false
% 2.61/1.00  
% 2.61/1.00  ------ Global Options
% 2.61/1.00  
% 2.61/1.00  --schedule                              default
% 2.61/1.00  --add_important_lit                     false
% 2.61/1.00  --prop_solver_per_cl                    1000
% 2.61/1.00  --min_unsat_core                        false
% 2.61/1.00  --soft_assumptions                      false
% 2.61/1.00  --soft_lemma_size                       3
% 2.61/1.00  --prop_impl_unit_size                   0
% 2.61/1.00  --prop_impl_unit                        []
% 2.61/1.00  --share_sel_clauses                     true
% 2.61/1.00  --reset_solvers                         false
% 2.61/1.00  --bc_imp_inh                            [conj_cone]
% 2.61/1.00  --conj_cone_tolerance                   3.
% 2.61/1.00  --extra_neg_conj                        none
% 2.61/1.00  --large_theory_mode                     true
% 2.61/1.00  --prolific_symb_bound                   200
% 2.61/1.00  --lt_threshold                          2000
% 2.61/1.00  --clause_weak_htbl                      true
% 2.61/1.00  --gc_record_bc_elim                     false
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing Options
% 2.61/1.00  
% 2.61/1.00  --preprocessing_flag                    true
% 2.61/1.00  --time_out_prep_mult                    0.1
% 2.61/1.00  --splitting_mode                        input
% 2.61/1.00  --splitting_grd                         true
% 2.61/1.00  --splitting_cvd                         false
% 2.61/1.00  --splitting_cvd_svl                     false
% 2.61/1.00  --splitting_nvd                         32
% 2.61/1.00  --sub_typing                            true
% 2.61/1.00  --prep_gs_sim                           true
% 2.61/1.00  --prep_unflatten                        true
% 2.61/1.00  --prep_res_sim                          true
% 2.61/1.00  --prep_upred                            true
% 2.61/1.00  --prep_sem_filter                       exhaustive
% 2.61/1.00  --prep_sem_filter_out                   false
% 2.61/1.00  --pred_elim                             true
% 2.61/1.00  --res_sim_input                         true
% 2.61/1.00  --eq_ax_congr_red                       true
% 2.61/1.00  --pure_diseq_elim                       true
% 2.61/1.00  --brand_transform                       false
% 2.61/1.00  --non_eq_to_eq                          false
% 2.61/1.00  --prep_def_merge                        true
% 2.61/1.00  --prep_def_merge_prop_impl              false
% 2.61/1.00  --prep_def_merge_mbd                    true
% 2.61/1.00  --prep_def_merge_tr_red                 false
% 2.61/1.00  --prep_def_merge_tr_cl                  false
% 2.61/1.00  --smt_preprocessing                     true
% 2.61/1.00  --smt_ac_axioms                         fast
% 2.61/1.00  --preprocessed_out                      false
% 2.61/1.00  --preprocessed_stats                    false
% 2.61/1.00  
% 2.61/1.00  ------ Abstraction refinement Options
% 2.61/1.00  
% 2.61/1.00  --abstr_ref                             []
% 2.61/1.00  --abstr_ref_prep                        false
% 2.61/1.00  --abstr_ref_until_sat                   false
% 2.61/1.00  --abstr_ref_sig_restrict                funpre
% 2.61/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.00  --abstr_ref_under                       []
% 2.61/1.00  
% 2.61/1.00  ------ SAT Options
% 2.61/1.00  
% 2.61/1.00  --sat_mode                              false
% 2.61/1.00  --sat_fm_restart_options                ""
% 2.61/1.00  --sat_gr_def                            false
% 2.61/1.00  --sat_epr_types                         true
% 2.61/1.00  --sat_non_cyclic_types                  false
% 2.61/1.00  --sat_finite_models                     false
% 2.61/1.00  --sat_fm_lemmas                         false
% 2.61/1.00  --sat_fm_prep                           false
% 2.61/1.00  --sat_fm_uc_incr                        true
% 2.61/1.00  --sat_out_model                         small
% 2.61/1.00  --sat_out_clauses                       false
% 2.61/1.00  
% 2.61/1.00  ------ QBF Options
% 2.61/1.00  
% 2.61/1.00  --qbf_mode                              false
% 2.61/1.00  --qbf_elim_univ                         false
% 2.61/1.00  --qbf_dom_inst                          none
% 2.61/1.00  --qbf_dom_pre_inst                      false
% 2.61/1.00  --qbf_sk_in                             false
% 2.61/1.00  --qbf_pred_elim                         true
% 2.61/1.00  --qbf_split                             512
% 2.61/1.00  
% 2.61/1.00  ------ BMC1 Options
% 2.61/1.00  
% 2.61/1.00  --bmc1_incremental                      false
% 2.61/1.00  --bmc1_axioms                           reachable_all
% 2.61/1.00  --bmc1_min_bound                        0
% 2.61/1.00  --bmc1_max_bound                        -1
% 2.61/1.00  --bmc1_max_bound_default                -1
% 2.61/1.00  --bmc1_symbol_reachability              true
% 2.61/1.00  --bmc1_property_lemmas                  false
% 2.61/1.00  --bmc1_k_induction                      false
% 2.61/1.00  --bmc1_non_equiv_states                 false
% 2.61/1.00  --bmc1_deadlock                         false
% 2.61/1.00  --bmc1_ucm                              false
% 2.61/1.00  --bmc1_add_unsat_core                   none
% 2.61/1.00  --bmc1_unsat_core_children              false
% 2.61/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.00  --bmc1_out_stat                         full
% 2.61/1.00  --bmc1_ground_init                      false
% 2.61/1.00  --bmc1_pre_inst_next_state              false
% 2.61/1.00  --bmc1_pre_inst_state                   false
% 2.61/1.00  --bmc1_pre_inst_reach_state             false
% 2.61/1.00  --bmc1_out_unsat_core                   false
% 2.61/1.00  --bmc1_aig_witness_out                  false
% 2.61/1.00  --bmc1_verbose                          false
% 2.61/1.00  --bmc1_dump_clauses_tptp                false
% 2.61/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.00  --bmc1_dump_file                        -
% 2.61/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.00  --bmc1_ucm_extend_mode                  1
% 2.61/1.00  --bmc1_ucm_init_mode                    2
% 2.61/1.00  --bmc1_ucm_cone_mode                    none
% 2.61/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.00  --bmc1_ucm_relax_model                  4
% 2.61/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.00  --bmc1_ucm_layered_model                none
% 2.61/1.00  --bmc1_ucm_max_lemma_size               10
% 2.61/1.00  
% 2.61/1.00  ------ AIG Options
% 2.61/1.00  
% 2.61/1.00  --aig_mode                              false
% 2.61/1.00  
% 2.61/1.00  ------ Instantiation Options
% 2.61/1.00  
% 2.61/1.00  --instantiation_flag                    true
% 2.61/1.00  --inst_sos_flag                         false
% 2.61/1.00  --inst_sos_phase                        true
% 2.61/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel_side                     num_symb
% 2.61/1.00  --inst_solver_per_active                1400
% 2.61/1.00  --inst_solver_calls_frac                1.
% 2.61/1.00  --inst_passive_queue_type               priority_queues
% 2.61/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.00  --inst_passive_queues_freq              [25;2]
% 2.61/1.00  --inst_dismatching                      true
% 2.61/1.00  --inst_eager_unprocessed_to_passive     true
% 2.61/1.00  --inst_prop_sim_given                   true
% 2.61/1.00  --inst_prop_sim_new                     false
% 2.61/1.00  --inst_subs_new                         false
% 2.61/1.00  --inst_eq_res_simp                      false
% 2.61/1.00  --inst_subs_given                       false
% 2.61/1.00  --inst_orphan_elimination               true
% 2.61/1.00  --inst_learning_loop_flag               true
% 2.61/1.00  --inst_learning_start                   3000
% 2.61/1.00  --inst_learning_factor                  2
% 2.61/1.00  --inst_start_prop_sim_after_learn       3
% 2.61/1.00  --inst_sel_renew                        solver
% 2.61/1.00  --inst_lit_activity_flag                true
% 2.61/1.00  --inst_restr_to_given                   false
% 2.61/1.00  --inst_activity_threshold               500
% 2.61/1.00  --inst_out_proof                        true
% 2.61/1.00  
% 2.61/1.00  ------ Resolution Options
% 2.61/1.00  
% 2.61/1.00  --resolution_flag                       true
% 2.61/1.00  --res_lit_sel                           adaptive
% 2.61/1.00  --res_lit_sel_side                      none
% 2.61/1.00  --res_ordering                          kbo
% 2.61/1.00  --res_to_prop_solver                    active
% 2.61/1.00  --res_prop_simpl_new                    false
% 2.61/1.00  --res_prop_simpl_given                  true
% 2.61/1.00  --res_passive_queue_type                priority_queues
% 2.61/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.00  --res_passive_queues_freq               [15;5]
% 2.61/1.00  --res_forward_subs                      full
% 2.61/1.00  --res_backward_subs                     full
% 2.61/1.00  --res_forward_subs_resolution           true
% 2.61/1.00  --res_backward_subs_resolution          true
% 2.61/1.00  --res_orphan_elimination                true
% 2.61/1.00  --res_time_limit                        2.
% 2.61/1.00  --res_out_proof                         true
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Options
% 2.61/1.00  
% 2.61/1.00  --superposition_flag                    true
% 2.61/1.00  --sup_passive_queue_type                priority_queues
% 2.61/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.00  --demod_completeness_check              fast
% 2.61/1.00  --demod_use_ground                      true
% 2.61/1.00  --sup_to_prop_solver                    passive
% 2.61/1.00  --sup_prop_simpl_new                    true
% 2.61/1.00  --sup_prop_simpl_given                  true
% 2.61/1.00  --sup_fun_splitting                     false
% 2.61/1.00  --sup_smt_interval                      50000
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Simplification Setup
% 2.61/1.00  
% 2.61/1.00  --sup_indices_passive                   []
% 2.61/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_full_bw                           [BwDemod]
% 2.61/1.00  --sup_immed_triv                        [TrivRules]
% 2.61/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_immed_bw_main                     []
% 2.61/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  
% 2.61/1.00  ------ Combination Options
% 2.61/1.00  
% 2.61/1.00  --comb_res_mult                         3
% 2.61/1.00  --comb_sup_mult                         2
% 2.61/1.00  --comb_inst_mult                        10
% 2.61/1.00  
% 2.61/1.00  ------ Debug Options
% 2.61/1.00  
% 2.61/1.00  --dbg_backtrace                         false
% 2.61/1.00  --dbg_dump_prop_clauses                 false
% 2.61/1.00  --dbg_dump_prop_clauses_file            -
% 2.61/1.00  --dbg_out_stat                          false
% 2.61/1.00  ------ Parsing...
% 2.61/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/1.00  ------ Proving...
% 2.61/1.00  ------ Problem Properties 
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  clauses                                 25
% 2.61/1.00  conjectures                             5
% 2.61/1.00  EPR                                     2
% 2.61/1.00  Horn                                    25
% 2.61/1.00  unary                                   10
% 2.61/1.00  binary                                  1
% 2.61/1.00  lits                                    82
% 2.61/1.00  lits eq                                 18
% 2.61/1.00  fd_pure                                 0
% 2.61/1.00  fd_pseudo                               0
% 2.61/1.00  fd_cond                                 0
% 2.61/1.00  fd_pseudo_cond                          1
% 2.61/1.00  AC symbols                              0
% 2.61/1.00  
% 2.61/1.00  ------ Schedule dynamic 5 is on 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  ------ 
% 2.61/1.00  Current options:
% 2.61/1.00  ------ 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options
% 2.61/1.00  
% 2.61/1.00  --out_options                           all
% 2.61/1.00  --tptp_safe_out                         true
% 2.61/1.00  --problem_path                          ""
% 2.61/1.00  --include_path                          ""
% 2.61/1.00  --clausifier                            res/vclausify_rel
% 2.61/1.00  --clausifier_options                    --mode clausify
% 2.61/1.00  --stdin                                 false
% 2.61/1.00  --stats_out                             all
% 2.61/1.00  
% 2.61/1.00  ------ General Options
% 2.61/1.00  
% 2.61/1.00  --fof                                   false
% 2.61/1.00  --time_out_real                         305.
% 2.61/1.00  --time_out_virtual                      -1.
% 2.61/1.00  --symbol_type_check                     false
% 2.61/1.00  --clausify_out                          false
% 2.61/1.00  --sig_cnt_out                           false
% 2.61/1.00  --trig_cnt_out                          false
% 2.61/1.00  --trig_cnt_out_tolerance                1.
% 2.61/1.00  --trig_cnt_out_sk_spl                   false
% 2.61/1.00  --abstr_cl_out                          false
% 2.61/1.00  
% 2.61/1.00  ------ Global Options
% 2.61/1.00  
% 2.61/1.00  --schedule                              default
% 2.61/1.00  --add_important_lit                     false
% 2.61/1.00  --prop_solver_per_cl                    1000
% 2.61/1.00  --min_unsat_core                        false
% 2.61/1.00  --soft_assumptions                      false
% 2.61/1.00  --soft_lemma_size                       3
% 2.61/1.00  --prop_impl_unit_size                   0
% 2.61/1.00  --prop_impl_unit                        []
% 2.61/1.00  --share_sel_clauses                     true
% 2.61/1.00  --reset_solvers                         false
% 2.61/1.00  --bc_imp_inh                            [conj_cone]
% 2.61/1.00  --conj_cone_tolerance                   3.
% 2.61/1.00  --extra_neg_conj                        none
% 2.61/1.00  --large_theory_mode                     true
% 2.61/1.00  --prolific_symb_bound                   200
% 2.61/1.00  --lt_threshold                          2000
% 2.61/1.00  --clause_weak_htbl                      true
% 2.61/1.00  --gc_record_bc_elim                     false
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing Options
% 2.61/1.00  
% 2.61/1.00  --preprocessing_flag                    true
% 2.61/1.00  --time_out_prep_mult                    0.1
% 2.61/1.00  --splitting_mode                        input
% 2.61/1.00  --splitting_grd                         true
% 2.61/1.00  --splitting_cvd                         false
% 2.61/1.00  --splitting_cvd_svl                     false
% 2.61/1.00  --splitting_nvd                         32
% 2.61/1.00  --sub_typing                            true
% 2.61/1.00  --prep_gs_sim                           true
% 2.61/1.00  --prep_unflatten                        true
% 2.61/1.00  --prep_res_sim                          true
% 2.61/1.00  --prep_upred                            true
% 2.61/1.00  --prep_sem_filter                       exhaustive
% 2.61/1.00  --prep_sem_filter_out                   false
% 2.61/1.00  --pred_elim                             true
% 2.61/1.00  --res_sim_input                         true
% 2.61/1.00  --eq_ax_congr_red                       true
% 2.61/1.00  --pure_diseq_elim                       true
% 2.61/1.00  --brand_transform                       false
% 2.61/1.00  --non_eq_to_eq                          false
% 2.61/1.00  --prep_def_merge                        true
% 2.61/1.00  --prep_def_merge_prop_impl              false
% 2.61/1.00  --prep_def_merge_mbd                    true
% 2.61/1.00  --prep_def_merge_tr_red                 false
% 2.61/1.00  --prep_def_merge_tr_cl                  false
% 2.61/1.00  --smt_preprocessing                     true
% 2.61/1.00  --smt_ac_axioms                         fast
% 2.61/1.00  --preprocessed_out                      false
% 2.61/1.00  --preprocessed_stats                    false
% 2.61/1.00  
% 2.61/1.00  ------ Abstraction refinement Options
% 2.61/1.00  
% 2.61/1.00  --abstr_ref                             []
% 2.61/1.00  --abstr_ref_prep                        false
% 2.61/1.00  --abstr_ref_until_sat                   false
% 2.61/1.00  --abstr_ref_sig_restrict                funpre
% 2.61/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.00  --abstr_ref_under                       []
% 2.61/1.00  
% 2.61/1.00  ------ SAT Options
% 2.61/1.00  
% 2.61/1.00  --sat_mode                              false
% 2.61/1.00  --sat_fm_restart_options                ""
% 2.61/1.00  --sat_gr_def                            false
% 2.61/1.00  --sat_epr_types                         true
% 2.61/1.00  --sat_non_cyclic_types                  false
% 2.61/1.00  --sat_finite_models                     false
% 2.61/1.00  --sat_fm_lemmas                         false
% 2.61/1.00  --sat_fm_prep                           false
% 2.61/1.00  --sat_fm_uc_incr                        true
% 2.61/1.00  --sat_out_model                         small
% 2.61/1.00  --sat_out_clauses                       false
% 2.61/1.00  
% 2.61/1.00  ------ QBF Options
% 2.61/1.00  
% 2.61/1.00  --qbf_mode                              false
% 2.61/1.00  --qbf_elim_univ                         false
% 2.61/1.00  --qbf_dom_inst                          none
% 2.61/1.00  --qbf_dom_pre_inst                      false
% 2.61/1.00  --qbf_sk_in                             false
% 2.61/1.00  --qbf_pred_elim                         true
% 2.61/1.00  --qbf_split                             512
% 2.61/1.00  
% 2.61/1.00  ------ BMC1 Options
% 2.61/1.00  
% 2.61/1.00  --bmc1_incremental                      false
% 2.61/1.00  --bmc1_axioms                           reachable_all
% 2.61/1.00  --bmc1_min_bound                        0
% 2.61/1.00  --bmc1_max_bound                        -1
% 2.61/1.00  --bmc1_max_bound_default                -1
% 2.61/1.00  --bmc1_symbol_reachability              true
% 2.61/1.00  --bmc1_property_lemmas                  false
% 2.61/1.00  --bmc1_k_induction                      false
% 2.61/1.00  --bmc1_non_equiv_states                 false
% 2.61/1.00  --bmc1_deadlock                         false
% 2.61/1.00  --bmc1_ucm                              false
% 2.61/1.00  --bmc1_add_unsat_core                   none
% 2.61/1.00  --bmc1_unsat_core_children              false
% 2.61/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.00  --bmc1_out_stat                         full
% 2.61/1.00  --bmc1_ground_init                      false
% 2.61/1.00  --bmc1_pre_inst_next_state              false
% 2.61/1.00  --bmc1_pre_inst_state                   false
% 2.61/1.00  --bmc1_pre_inst_reach_state             false
% 2.61/1.00  --bmc1_out_unsat_core                   false
% 2.61/1.00  --bmc1_aig_witness_out                  false
% 2.61/1.00  --bmc1_verbose                          false
% 2.61/1.00  --bmc1_dump_clauses_tptp                false
% 2.61/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.00  --bmc1_dump_file                        -
% 2.61/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.00  --bmc1_ucm_extend_mode                  1
% 2.61/1.00  --bmc1_ucm_init_mode                    2
% 2.61/1.00  --bmc1_ucm_cone_mode                    none
% 2.61/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.00  --bmc1_ucm_relax_model                  4
% 2.61/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.00  --bmc1_ucm_layered_model                none
% 2.61/1.00  --bmc1_ucm_max_lemma_size               10
% 2.61/1.00  
% 2.61/1.00  ------ AIG Options
% 2.61/1.00  
% 2.61/1.00  --aig_mode                              false
% 2.61/1.00  
% 2.61/1.00  ------ Instantiation Options
% 2.61/1.00  
% 2.61/1.00  --instantiation_flag                    true
% 2.61/1.00  --inst_sos_flag                         false
% 2.61/1.00  --inst_sos_phase                        true
% 2.61/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel_side                     none
% 2.61/1.00  --inst_solver_per_active                1400
% 2.61/1.00  --inst_solver_calls_frac                1.
% 2.61/1.00  --inst_passive_queue_type               priority_queues
% 2.61/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.00  --inst_passive_queues_freq              [25;2]
% 2.61/1.00  --inst_dismatching                      true
% 2.61/1.00  --inst_eager_unprocessed_to_passive     true
% 2.61/1.00  --inst_prop_sim_given                   true
% 2.61/1.00  --inst_prop_sim_new                     false
% 2.61/1.00  --inst_subs_new                         false
% 2.61/1.00  --inst_eq_res_simp                      false
% 2.61/1.00  --inst_subs_given                       false
% 2.61/1.00  --inst_orphan_elimination               true
% 2.61/1.00  --inst_learning_loop_flag               true
% 2.61/1.00  --inst_learning_start                   3000
% 2.61/1.00  --inst_learning_factor                  2
% 2.61/1.00  --inst_start_prop_sim_after_learn       3
% 2.61/1.00  --inst_sel_renew                        solver
% 2.61/1.00  --inst_lit_activity_flag                true
% 2.61/1.00  --inst_restr_to_given                   false
% 2.61/1.00  --inst_activity_threshold               500
% 2.61/1.00  --inst_out_proof                        true
% 2.61/1.00  
% 2.61/1.00  ------ Resolution Options
% 2.61/1.00  
% 2.61/1.00  --resolution_flag                       false
% 2.61/1.00  --res_lit_sel                           adaptive
% 2.61/1.00  --res_lit_sel_side                      none
% 2.61/1.00  --res_ordering                          kbo
% 2.61/1.00  --res_to_prop_solver                    active
% 2.61/1.00  --res_prop_simpl_new                    false
% 2.61/1.00  --res_prop_simpl_given                  true
% 2.61/1.00  --res_passive_queue_type                priority_queues
% 2.61/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.00  --res_passive_queues_freq               [15;5]
% 2.61/1.00  --res_forward_subs                      full
% 2.61/1.00  --res_backward_subs                     full
% 2.61/1.00  --res_forward_subs_resolution           true
% 2.61/1.00  --res_backward_subs_resolution          true
% 2.61/1.00  --res_orphan_elimination                true
% 2.61/1.00  --res_time_limit                        2.
% 2.61/1.00  --res_out_proof                         true
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Options
% 2.61/1.00  
% 2.61/1.00  --superposition_flag                    true
% 2.61/1.00  --sup_passive_queue_type                priority_queues
% 2.61/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.00  --demod_completeness_check              fast
% 2.61/1.00  --demod_use_ground                      true
% 2.61/1.00  --sup_to_prop_solver                    passive
% 2.61/1.00  --sup_prop_simpl_new                    true
% 2.61/1.00  --sup_prop_simpl_given                  true
% 2.61/1.00  --sup_fun_splitting                     false
% 2.61/1.00  --sup_smt_interval                      50000
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Simplification Setup
% 2.61/1.00  
% 2.61/1.00  --sup_indices_passive                   []
% 2.61/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_full_bw                           [BwDemod]
% 2.61/1.00  --sup_immed_triv                        [TrivRules]
% 2.61/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_immed_bw_main                     []
% 2.61/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  
% 2.61/1.00  ------ Combination Options
% 2.61/1.00  
% 2.61/1.00  --comb_res_mult                         3
% 2.61/1.00  --comb_sup_mult                         2
% 2.61/1.00  --comb_inst_mult                        10
% 2.61/1.00  
% 2.61/1.00  ------ Debug Options
% 2.61/1.00  
% 2.61/1.00  --dbg_backtrace                         false
% 2.61/1.00  --dbg_dump_prop_clauses                 false
% 2.61/1.00  --dbg_dump_prop_clauses_file            -
% 2.61/1.00  --dbg_out_stat                          false
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  ------ Proving...
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  % SZS status Theorem for theBenchmark.p
% 2.61/1.00  
% 2.61/1.00   Resolution empty clause
% 2.61/1.00  
% 2.61/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/1.00  
% 2.61/1.00  fof(f17,conjecture,(
% 2.61/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f18,negated_conjecture,(
% 2.61/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.61/1.00    inference(negated_conjecture,[],[f17])).
% 2.61/1.00  
% 2.61/1.00  fof(f44,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.61/1.00    inference(ennf_transformation,[],[f18])).
% 2.61/1.00  
% 2.61/1.00  fof(f45,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f44])).
% 2.61/1.00  
% 2.61/1.00  fof(f50,plain,(
% 2.61/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f49,plain,(
% 2.61/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f48,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f51,plain,(
% 2.61/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f50,f49,f48])).
% 2.61/1.00  
% 2.61/1.00  fof(f82,plain,(
% 2.61/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f14,axiom,(
% 2.61/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f39,plain,(
% 2.61/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.61/1.00    inference(ennf_transformation,[],[f14])).
% 2.61/1.00  
% 2.61/1.00  fof(f74,plain,(
% 2.61/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f39])).
% 2.61/1.00  
% 2.61/1.00  fof(f77,plain,(
% 2.61/1.00    l1_struct_0(sK0)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f79,plain,(
% 2.61/1.00    l1_struct_0(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f9,axiom,(
% 2.61/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f30,plain,(
% 2.61/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.00    inference(ennf_transformation,[],[f9])).
% 2.61/1.00  
% 2.61/1.00  fof(f64,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.00    inference(cnf_transformation,[],[f30])).
% 2.61/1.00  
% 2.61/1.00  fof(f83,plain,(
% 2.61/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f16,axiom,(
% 2.61/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f42,plain,(
% 2.61/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.00    inference(ennf_transformation,[],[f16])).
% 2.61/1.00  
% 2.61/1.00  fof(f43,plain,(
% 2.61/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.00    inference(flattening,[],[f42])).
% 2.61/1.00  
% 2.61/1.00  fof(f76,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f43])).
% 2.61/1.00  
% 2.61/1.00  fof(f80,plain,(
% 2.61/1.00    v1_funct_1(sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f84,plain,(
% 2.61/1.00    v2_funct_1(sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f81,plain,(
% 2.61/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f12,axiom,(
% 2.61/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f35,plain,(
% 2.61/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.00    inference(ennf_transformation,[],[f12])).
% 2.61/1.00  
% 2.61/1.00  fof(f36,plain,(
% 2.61/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.00    inference(flattening,[],[f35])).
% 2.61/1.00  
% 2.61/1.00  fof(f47,plain,(
% 2.61/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.00    inference(nnf_transformation,[],[f36])).
% 2.61/1.00  
% 2.61/1.00  fof(f70,plain,(
% 2.61/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f47])).
% 2.61/1.00  
% 2.61/1.00  fof(f87,plain,(
% 2.61/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.61/1.00    inference(equality_resolution,[],[f70])).
% 2.61/1.00  
% 2.61/1.00  fof(f85,plain,(
% 2.61/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f13,axiom,(
% 2.61/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f37,plain,(
% 2.61/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.00    inference(ennf_transformation,[],[f13])).
% 2.61/1.00  
% 2.61/1.00  fof(f38,plain,(
% 2.61/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.00    inference(flattening,[],[f37])).
% 2.61/1.00  
% 2.61/1.00  fof(f71,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f38])).
% 2.61/1.00  
% 2.61/1.00  fof(f1,axiom,(
% 2.61/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f20,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.61/1.00    inference(ennf_transformation,[],[f1])).
% 2.61/1.00  
% 2.61/1.00  fof(f52,plain,(
% 2.61/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f20])).
% 2.61/1.00  
% 2.61/1.00  fof(f2,axiom,(
% 2.61/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f53,plain,(
% 2.61/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.61/1.00    inference(cnf_transformation,[],[f2])).
% 2.61/1.00  
% 2.61/1.00  fof(f72,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f38])).
% 2.61/1.00  
% 2.61/1.00  fof(f5,axiom,(
% 2.61/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f23,plain,(
% 2.61/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f5])).
% 2.61/1.00  
% 2.61/1.00  fof(f24,plain,(
% 2.61/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.00    inference(flattening,[],[f23])).
% 2.61/1.00  
% 2.61/1.00  fof(f59,plain,(
% 2.61/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f24])).
% 2.61/1.00  
% 2.61/1.00  fof(f4,axiom,(
% 2.61/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f21,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f4])).
% 2.61/1.00  
% 2.61/1.00  fof(f22,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.00    inference(flattening,[],[f21])).
% 2.61/1.00  
% 2.61/1.00  fof(f56,plain,(
% 2.61/1.00    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f22])).
% 2.61/1.00  
% 2.61/1.00  fof(f73,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f38])).
% 2.61/1.00  
% 2.61/1.00  fof(f6,axiom,(
% 2.61/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f25,plain,(
% 2.61/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f6])).
% 2.61/1.00  
% 2.61/1.00  fof(f26,plain,(
% 2.61/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.00    inference(flattening,[],[f25])).
% 2.61/1.00  
% 2.61/1.00  fof(f61,plain,(
% 2.61/1.00    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f26])).
% 2.61/1.00  
% 2.61/1.00  fof(f3,axiom,(
% 2.61/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f55,plain,(
% 2.61/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.61/1.00    inference(cnf_transformation,[],[f3])).
% 2.61/1.00  
% 2.61/1.00  fof(f10,axiom,(
% 2.61/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f31,plain,(
% 2.61/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.00    inference(ennf_transformation,[],[f10])).
% 2.61/1.00  
% 2.61/1.00  fof(f32,plain,(
% 2.61/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.00    inference(flattening,[],[f31])).
% 2.61/1.00  
% 2.61/1.00  fof(f66,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f32])).
% 2.61/1.00  
% 2.61/1.00  fof(f15,axiom,(
% 2.61/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f40,plain,(
% 2.61/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f15])).
% 2.61/1.00  
% 2.61/1.00  fof(f41,plain,(
% 2.61/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f40])).
% 2.61/1.00  
% 2.61/1.00  fof(f75,plain,(
% 2.61/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f41])).
% 2.61/1.00  
% 2.61/1.00  fof(f78,plain,(
% 2.61/1.00    ~v2_struct_0(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f51])).
% 2.61/1.00  
% 2.61/1.00  fof(f11,axiom,(
% 2.61/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f33,plain,(
% 2.61/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.61/1.00    inference(ennf_transformation,[],[f11])).
% 2.61/1.00  
% 2.61/1.00  fof(f34,plain,(
% 2.61/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.00    inference(flattening,[],[f33])).
% 2.61/1.00  
% 2.61/1.00  fof(f46,plain,(
% 2.61/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.00    inference(nnf_transformation,[],[f34])).
% 2.61/1.00  
% 2.61/1.00  fof(f67,plain,(
% 2.61/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f46])).
% 2.61/1.00  
% 2.61/1.00  fof(f8,axiom,(
% 2.61/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f19,plain,(
% 2.61/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.61/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.61/1.00  
% 2.61/1.00  fof(f29,plain,(
% 2.61/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.00    inference(ennf_transformation,[],[f19])).
% 2.61/1.00  
% 2.61/1.00  fof(f63,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.00    inference(cnf_transformation,[],[f29])).
% 2.61/1.00  
% 2.61/1.00  fof(f7,axiom,(
% 2.61/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f27,plain,(
% 2.61/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f7])).
% 2.61/1.00  
% 2.61/1.00  fof(f28,plain,(
% 2.61/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.00    inference(flattening,[],[f27])).
% 2.61/1.00  
% 2.61/1.00  fof(f62,plain,(
% 2.61/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f28])).
% 2.61/1.00  
% 2.61/1.00  cnf(c_28,negated_conjecture,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_666,negated_conjecture,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1143,plain,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_22,plain,
% 2.61/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_33,negated_conjecture,
% 2.61/1.00      ( l1_struct_0(sK0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_383,plain,
% 2.61/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_384,plain,
% 2.61/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_383]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_662,plain,
% 2.61/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_384]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_31,negated_conjecture,
% 2.61/1.00      ( l1_struct_0(sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_378,plain,
% 2.61/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_379,plain,
% 2.61/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_378]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_663,plain,
% 2.61/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_379]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1168,plain,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_1143,c_662,c_663]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_12,plain,
% 2.61/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_673,plain,
% 2.61/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.00      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1137,plain,
% 2.61/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.61/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1574,plain,
% 2.61/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_1168,c_1137]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_27,negated_conjecture,
% 2.61/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_667,negated_conjecture,
% 2.61/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1165,plain,
% 2.61/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_667,c_662,c_663]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1576,plain,
% 2.61/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_1574,c_1165]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1622,plain,
% 2.61/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_1576,c_1574]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_24,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | ~ v2_funct_1(X0)
% 2.61/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.61/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_669,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.61/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.00      | ~ v1_funct_1(X0_53)
% 2.61/1.00      | ~ v2_funct_1(X0_53)
% 2.61/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.61/1.00      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1141,plain,
% 2.61/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.61/1.00      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
% 2.61/1.00      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.61/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.61/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2458,plain,
% 2.61/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.61/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.00      | v1_funct_1(sK2) != iProver_top
% 2.61/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_1622,c_1141]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_30,negated_conjecture,
% 2.61/1.00      ( v1_funct_1(sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_37,plain,
% 2.61/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_26,negated_conjecture,
% 2.61/1.00      ( v2_funct_1(sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_40,plain,
% 2.61/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1624,plain,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_1576,c_1168]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_29,negated_conjecture,
% 2.61/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.61/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_665,negated_conjecture,
% 2.61/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1144,plain,
% 2.61/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1162,plain,
% 2.61/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_1144,c_662,c_663]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1625,plain,
% 2.61/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_1576,c_1162]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2800,plain,
% 2.61/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_2458,c_37,c_40,c_1624,c_1625]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_17,plain,
% 2.61/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.61/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.61/1.00      | ~ v1_funct_1(X2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_25,negated_conjecture,
% 2.61/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_487,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.61/1.00      | u1_struct_0(sK1) != X2
% 2.61/1.00      | u1_struct_0(sK0) != X1
% 2.61/1.00      | sK2 != X0 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_488,plain,
% 2.61/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.61/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_487]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_660,plain,
% 2.61/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.61/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_488]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1147,plain,
% 2.61/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.61/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.61/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1307,plain,
% 2.61/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.61/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.61/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.61/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_1147,c_662,c_663]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1623,plain,
% 2.61/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.61/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_1576,c_1307]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2803,plain,
% 2.61/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.61/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_2800,c_1623]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_38,plain,
% 2.61/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_39,plain,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_21,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.61/1.00      | ~ v2_funct_1(X0)
% 2.61/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_670,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.61/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.00      | ~ v1_funct_1(X0_53)
% 2.61/1.00      | v1_funct_1(k2_funct_1(X0_53))
% 2.61/1.00      | ~ v2_funct_1(X0_53)
% 2.61/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1432,plain,
% 2.61/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.00      | v1_funct_1(k2_funct_1(sK2))
% 2.61/1.00      | ~ v1_funct_1(sK2)
% 2.61/1.00      | ~ v2_funct_1(sK2)
% 2.61/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_670]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1433,plain,
% 2.61/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.61/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.61/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.00      | v1_funct_1(sK2) != iProver_top
% 2.61/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_1432]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_0,plain,
% 2.61/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_684,plain,
% 2.61/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.61/1.00      | ~ v1_relat_1(X1_53)
% 2.61/1.00      | v1_relat_1(X0_53) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1374,plain,
% 2.61/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.00      | v1_relat_1(X0_53)
% 2.61/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_684]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1555,plain,
% 2.61/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.61/1.00      | v1_relat_1(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_1374]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1556,plain,
% 2.61/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.61/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_1555]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1,plain,
% 2.61/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.61/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_683,plain,
% 2.61/1.00      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1577,plain,
% 2.61/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_683]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1578,plain,
% 2.61/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_690,plain,
% 2.61/1.00      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.61/1.00      theory(equality) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1491,plain,
% 2.61/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_54
% 2.61/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.61/1.00      | u1_struct_0(sK1) != X0_54 ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_690]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1582,plain,
% 2.61/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.61/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.61/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_1491]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_20,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | ~ v2_funct_1(X0)
% 2.61/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_671,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.61/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
% 2.61/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.00      | ~ v1_funct_1(X0_53)
% 2.61/1.00      | ~ v2_funct_1(X0_53)
% 2.61/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1139,plain,
% 2.61/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.61/1.00      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.61/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
% 2.61/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.61/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2449,plain,
% 2.61/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.61/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.00      | v1_funct_1(sK2) != iProver_top
% 2.61/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_1622,c_1139]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_664,negated_conjecture,
% 2.61/1.00      ( v1_funct_1(sK2) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1145,plain,
% 2.61/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6,plain,
% 2.61/1.00      ( ~ v1_funct_1(X0)
% 2.61/1.00      | ~ v2_funct_1(X0)
% 2.61/1.00      | ~ v1_relat_1(X0)
% 2.61/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_678,plain,
% 2.61/1.00      ( ~ v1_funct_1(X0_53)
% 2.61/1.00      | ~ v2_funct_1(X0_53)
% 2.61/1.00      | ~ v1_relat_1(X0_53)
% 2.61/1.00      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.61/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1132,plain,
% 2.61/1.00      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 2.61/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.61/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_1845,plain,
% 2.61/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.61/1.00      | v2_funct_1(sK2) != iProver_top
% 2.61/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_1145,c_1132]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_736,plain,
% 2.61/1.00      ( ~ v1_funct_1(sK2)
% 2.61/1.00      | ~ v2_funct_1(sK2)
% 2.61/1.00      | ~ v1_relat_1(sK2)
% 2.61/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_678]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2020,plain,
% 2.61/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_1845,c_30,c_28,c_26,c_736,c_1555,c_1577]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5,plain,
% 2.61/1.00      ( ~ v1_funct_1(X0)
% 2.61/1.00      | ~ v1_funct_1(X1)
% 2.61/1.00      | v2_funct_1(X0)
% 2.61/1.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.61/1.00      | ~ v1_relat_1(X1)
% 2.61/1.00      | ~ v1_relat_1(X0)
% 2.61/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_679,plain,
% 2.61/1.00      ( ~ v1_funct_1(X0_53)
% 2.61/1.00      | ~ v1_funct_1(X1_53)
% 2.61/1.00      | v2_funct_1(X0_53)
% 2.61/1.00      | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
% 2.61/1.00      | ~ v1_relat_1(X0_53)
% 2.61/1.00      | ~ v1_relat_1(X1_53)
% 2.61/1.01      | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1131,plain,
% 2.61/1.01      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_funct_1(X1_53) != iProver_top
% 2.61/1.01      | v2_funct_1(X1_53) = iProver_top
% 2.61/1.01      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 2.61/1.01      | v1_relat_1(X1_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2257,plain,
% 2.61/1.01      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.61/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top
% 2.61/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_2020,c_1131]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_19,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_672,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.61/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.61/1.01      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.61/1.01      | ~ v1_funct_1(X0_53)
% 2.61/1.01      | ~ v2_funct_1(X0_53)
% 2.61/1.01      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1445,plain,
% 2.61/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v2_funct_1(sK2)
% 2.61/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_672]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1446,plain,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.61/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_funct_1(sK2) != iProver_top
% 2.61/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1647,plain,
% 2.61/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.61/1.01      | v1_relat_1(k2_funct_1(sK2)) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_1374]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1651,plain,
% 2.61/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.61/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 2.61/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2362,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_683]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2363,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_2362]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2597,plain,
% 2.61/1.01      ( v1_relat_1(X0_53) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.61/1.01      | k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2257,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1446,c_1582,
% 2.61/1.01                 c_1651,c_2363]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2598,plain,
% 2.61/1.01      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(renaming,[status(thm)],[c_2597]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2609,plain,
% 2.61/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.61/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(equality_resolution,[status(thm)],[c_2598]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_8,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_676,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0_53)
% 2.61/1.01      | ~ v2_funct_1(X0_53)
% 2.61/1.01      | ~ v1_relat_1(X0_53)
% 2.61/1.01      | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1134,plain,
% 2.61/1.01      ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1926,plain,
% 2.61/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 2.61/1.01      | v2_funct_1(sK2) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1145,c_1134]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_742,plain,
% 2.61/1.01      ( ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v2_funct_1(sK2)
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_676]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2091,plain,
% 2.61/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_1926,c_30,c_28,c_26,c_742,c_1555,c_1577]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2614,plain,
% 2.61/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_2609,c_2091]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2621,plain,
% 2.61/1.01      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2614,c_37,c_39,c_1556,c_1578]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2622,plain,
% 2.61/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.01      | v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top ),
% 2.61/1.01      inference(renaming,[status(thm)],[c_2621]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2,plain,
% 2.61/1.01      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_682,plain,
% 2.61/1.01      ( v2_funct_1(k6_relat_1(X0_54)) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1128,plain,
% 2.61/1.01      ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2627,plain,
% 2.61/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.61/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2622,c_1128]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1138,plain,
% 2.61/1.01      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.61/1.01      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v2_funct_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2812,plain,
% 2.61/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.01      | v1_funct_1(sK2) != iProver_top
% 2.61/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1622,c_1138]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_13,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | v1_xboole_0(X2)
% 2.61/1.01      | ~ v1_funct_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_23,plain,
% 2.61/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_32,negated_conjecture,
% 2.61/1.01      ( ~ v2_struct_0(sK1) ),
% 2.61/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_365,plain,
% 2.61/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_366,plain,
% 2.61/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_365]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_46,plain,
% 2.61/1.01      ( v2_struct_0(sK1)
% 2.61/1.01      | ~ l1_struct_0(sK1)
% 2.61/1.01      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_368,plain,
% 2.61/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_366,c_32,c_31,c_46]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_390,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | k2_struct_0(sK1) != X2 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_368]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_391,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_390]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_16,plain,
% 2.61/1.01      ( ~ v1_partfun1(X0,X1)
% 2.61/1.01      | ~ v4_relat_1(X0,X1)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(X0) = X1 ),
% 2.61/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_452,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.61/1.01      | ~ v4_relat_1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(X0) = X1 ),
% 2.61/1.01      inference(resolution,[status(thm)],[c_391,c_16]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_11,plain,
% 2.61/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.61/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_468,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(X0) = X1 ),
% 2.61/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_452,c_11]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_661,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
% 2.61/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0_53)
% 2.61/1.01      | ~ v1_relat_1(X0_53)
% 2.61/1.01      | k1_relat_1(X0_53) = X0_54 ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_468]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1146,plain,
% 2.61/1.01      ( k1_relat_1(X0_53) = X0_54
% 2.61/1.01      | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2845,plain,
% 2.61/1.01      ( k1_relat_1(X0_53) = X0_54
% 2.61/1.01      | v1_funct_2(X0_53,X0_54,k2_relat_1(sK2)) != iProver_top
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_relat_1(sK2)))) != iProver_top
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_1146,c_1576]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2854,plain,
% 2.61/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.61/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.01      | v1_funct_1(sK2) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1624,c_2845]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2857,plain,
% 2.61/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2812,c_37,c_40,c_1624,c_1625]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2862,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_2857,c_1137]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2869,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_2862,c_2020]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2955,plain,
% 2.61/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.61/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.61/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.61/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_2869,c_1141]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_10,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.61/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_674,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0_53)
% 2.61/1.01      | ~ v2_funct_1(X0_53)
% 2.61/1.01      | ~ v1_relat_1(X0_53)
% 2.61/1.01      | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1136,plain,
% 2.61/1.01      ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
% 2.61/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1838,plain,
% 2.61/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.61/1.01      | v2_funct_1(sK2) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1145,c_1136]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_748,plain,
% 2.61/1.01      ( ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v2_funct_1(sK2)
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_674]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2016,plain,
% 2.61/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_1838,c_30,c_28,c_26,c_748,c_1555,c_1577]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2978,plain,
% 2.61/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.61/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.61/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.61/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.61/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_2955,c_2016]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3444,plain,
% 2.61/1.01      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2803,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1556,c_1578,
% 2.61/1.01                 c_1582,c_1624,c_1625,c_2449,c_2627,c_2812,c_2854,c_2978]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3066,plain,
% 2.61/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2854,c_37,c_39,c_1556,c_1578,c_1625]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3062,plain,
% 2.61/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_2978,c_37,c_38,c_39,c_40,c_667,c_663,c_1433,c_1556,c_1578,
% 2.61/1.01                 c_1582,c_1624,c_1625,c_2449,c_2627,c_2812,c_2854]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3069,plain,
% 2.61/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_3066,c_3062]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3448,plain,
% 2.61/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_3444,c_3066,c_3069]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3074,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_3066,c_1624]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3076,plain,
% 2.61/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_3066,c_1625]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3452,plain,
% 2.61/1.01      ( $false ),
% 2.61/1.01      inference(forward_subsumption_resolution,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_3448,c_1145,c_3074,c_3076]) ).
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  ------                               Statistics
% 2.61/1.01  
% 2.61/1.01  ------ General
% 2.61/1.01  
% 2.61/1.01  abstr_ref_over_cycles:                  0
% 2.61/1.01  abstr_ref_under_cycles:                 0
% 2.61/1.01  gc_basic_clause_elim:                   0
% 2.61/1.01  forced_gc_time:                         0
% 2.61/1.01  parsing_time:                           0.01
% 2.61/1.01  unif_index_cands_time:                  0.
% 2.61/1.01  unif_index_add_time:                    0.
% 2.61/1.01  orderings_time:                         0.
% 2.61/1.01  out_proof_time:                         0.012
% 2.61/1.01  total_time:                             0.162
% 2.61/1.01  num_of_symbols:                         60
% 2.61/1.01  num_of_terms:                           3146
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing
% 2.61/1.01  
% 2.61/1.01  num_of_splits:                          0
% 2.61/1.01  num_of_split_atoms:                     0
% 2.61/1.01  num_of_reused_defs:                     0
% 2.61/1.01  num_eq_ax_congr_red:                    4
% 2.61/1.01  num_of_sem_filtered_clauses:            1
% 2.61/1.01  num_of_subtypes:                        4
% 2.61/1.01  monotx_restored_types:                  1
% 2.61/1.01  sat_num_of_epr_types:                   0
% 2.61/1.01  sat_num_of_non_cyclic_types:            0
% 2.61/1.01  sat_guarded_non_collapsed_types:        1
% 2.61/1.01  num_pure_diseq_elim:                    0
% 2.61/1.01  simp_replaced_by:                       0
% 2.61/1.01  res_preprocessed:                       147
% 2.61/1.01  prep_upred:                             0
% 2.61/1.01  prep_unflattend:                        15
% 2.61/1.01  smt_new_axioms:                         0
% 2.61/1.01  pred_elim_cands:                        5
% 2.61/1.01  pred_elim:                              6
% 2.61/1.01  pred_elim_cl:                           8
% 2.61/1.01  pred_elim_cycles:                       9
% 2.61/1.01  merged_defs:                            0
% 2.61/1.01  merged_defs_ncl:                        0
% 2.61/1.01  bin_hyper_res:                          0
% 2.61/1.01  prep_cycles:                            4
% 2.61/1.01  pred_elim_time:                         0.005
% 2.61/1.01  splitting_time:                         0.
% 2.61/1.01  sem_filter_time:                        0.
% 2.61/1.01  monotx_time:                            0.
% 2.61/1.01  subtype_inf_time:                       0.001
% 2.61/1.01  
% 2.61/1.01  ------ Problem properties
% 2.61/1.01  
% 2.61/1.01  clauses:                                25
% 2.61/1.01  conjectures:                            5
% 2.61/1.01  epr:                                    2
% 2.61/1.01  horn:                                   25
% 2.61/1.01  ground:                                 8
% 2.61/1.01  unary:                                  10
% 2.61/1.01  binary:                                 1
% 2.61/1.01  lits:                                   82
% 2.61/1.01  lits_eq:                                18
% 2.61/1.01  fd_pure:                                0
% 2.61/1.01  fd_pseudo:                              0
% 2.61/1.01  fd_cond:                                0
% 2.61/1.01  fd_pseudo_cond:                         1
% 2.61/1.01  ac_symbols:                             0
% 2.61/1.01  
% 2.61/1.01  ------ Propositional Solver
% 2.61/1.01  
% 2.61/1.01  prop_solver_calls:                      29
% 2.61/1.01  prop_fast_solver_calls:                 1184
% 2.61/1.01  smt_solver_calls:                       0
% 2.61/1.01  smt_fast_solver_calls:                  0
% 2.61/1.01  prop_num_of_clauses:                    1168
% 2.61/1.01  prop_preprocess_simplified:             4815
% 2.61/1.01  prop_fo_subsumed:                       52
% 2.61/1.01  prop_solver_time:                       0.
% 2.61/1.01  smt_solver_time:                        0.
% 2.61/1.01  smt_fast_solver_time:                   0.
% 2.61/1.01  prop_fast_solver_time:                  0.
% 2.61/1.01  prop_unsat_core_time:                   0.
% 2.61/1.01  
% 2.61/1.01  ------ QBF
% 2.61/1.01  
% 2.61/1.01  qbf_q_res:                              0
% 2.61/1.01  qbf_num_tautologies:                    0
% 2.61/1.01  qbf_prep_cycles:                        0
% 2.61/1.01  
% 2.61/1.01  ------ BMC1
% 2.61/1.01  
% 2.61/1.01  bmc1_current_bound:                     -1
% 2.61/1.01  bmc1_last_solved_bound:                 -1
% 2.61/1.01  bmc1_unsat_core_size:                   -1
% 2.61/1.01  bmc1_unsat_core_parents_size:           -1
% 2.61/1.01  bmc1_merge_next_fun:                    0
% 2.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.61/1.01  
% 2.61/1.01  ------ Instantiation
% 2.61/1.01  
% 2.61/1.01  inst_num_of_clauses:                    406
% 2.61/1.01  inst_num_in_passive:                    110
% 2.61/1.01  inst_num_in_active:                     264
% 2.61/1.01  inst_num_in_unprocessed:                32
% 2.61/1.01  inst_num_of_loops:                      300
% 2.61/1.01  inst_num_of_learning_restarts:          0
% 2.61/1.01  inst_num_moves_active_passive:          31
% 2.61/1.01  inst_lit_activity:                      0
% 2.61/1.01  inst_lit_activity_moves:                0
% 2.61/1.01  inst_num_tautologies:                   0
% 2.61/1.01  inst_num_prop_implied:                  0
% 2.61/1.01  inst_num_existing_simplified:           0
% 2.61/1.01  inst_num_eq_res_simplified:             0
% 2.61/1.01  inst_num_child_elim:                    0
% 2.61/1.01  inst_num_of_dismatching_blockings:      74
% 2.61/1.01  inst_num_of_non_proper_insts:           437
% 2.61/1.01  inst_num_of_duplicates:                 0
% 2.61/1.01  inst_inst_num_from_inst_to_res:         0
% 2.61/1.01  inst_dismatching_checking_time:         0.
% 2.61/1.01  
% 2.61/1.01  ------ Resolution
% 2.61/1.01  
% 2.61/1.01  res_num_of_clauses:                     0
% 2.61/1.01  res_num_in_passive:                     0
% 2.61/1.01  res_num_in_active:                      0
% 2.61/1.01  res_num_of_loops:                       151
% 2.61/1.01  res_forward_subset_subsumed:            52
% 2.61/1.01  res_backward_subset_subsumed:           0
% 2.61/1.01  res_forward_subsumed:                   0
% 2.61/1.01  res_backward_subsumed:                  0
% 2.61/1.01  res_forward_subsumption_resolution:     1
% 2.61/1.01  res_backward_subsumption_resolution:    0
% 2.61/1.01  res_clause_to_clause_subsumption:       73
% 2.61/1.01  res_orphan_elimination:                 0
% 2.61/1.01  res_tautology_del:                      62
% 2.61/1.01  res_num_eq_res_simplified:              0
% 2.61/1.01  res_num_sel_changes:                    0
% 2.61/1.01  res_moves_from_active_to_pass:          0
% 2.61/1.01  
% 2.61/1.01  ------ Superposition
% 2.61/1.01  
% 2.61/1.01  sup_time_total:                         0.
% 2.61/1.01  sup_time_generating:                    0.
% 2.61/1.01  sup_time_sim_full:                      0.
% 2.61/1.01  sup_time_sim_immed:                     0.
% 2.61/1.01  
% 2.61/1.01  sup_num_of_clauses:                     45
% 2.61/1.01  sup_num_in_active:                      42
% 2.61/1.01  sup_num_in_passive:                     3
% 2.61/1.01  sup_num_of_loops:                       58
% 2.61/1.01  sup_fw_superposition:                   18
% 2.61/1.01  sup_bw_superposition:                   26
% 2.61/1.01  sup_immediate_simplified:               23
% 2.61/1.01  sup_given_eliminated:                   0
% 2.61/1.01  comparisons_done:                       0
% 2.61/1.01  comparisons_avoided:                    0
% 2.61/1.01  
% 2.61/1.01  ------ Simplifications
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  sim_fw_subset_subsumed:                 8
% 2.61/1.01  sim_bw_subset_subsumed:                 0
% 2.61/1.01  sim_fw_subsumed:                        5
% 2.61/1.01  sim_bw_subsumed:                        0
% 2.61/1.01  sim_fw_subsumption_res:                 4
% 2.61/1.01  sim_bw_subsumption_res:                 0
% 2.61/1.01  sim_tautology_del:                      0
% 2.61/1.01  sim_eq_tautology_del:                   7
% 2.61/1.01  sim_eq_res_simp:                        0
% 2.61/1.01  sim_fw_demodulated:                     0
% 2.61/1.01  sim_bw_demodulated:                     16
% 2.61/1.01  sim_light_normalised:                   21
% 2.61/1.01  sim_joinable_taut:                      0
% 2.61/1.01  sim_joinable_simp:                      0
% 2.61/1.01  sim_ac_normalised:                      0
% 2.61/1.01  sim_smt_subsumption:                    0
% 2.61/1.01  
%------------------------------------------------------------------------------
