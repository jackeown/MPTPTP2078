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
% DateTime   : Thu Dec  3 12:17:44 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  148 (2159 expanded)
%              Number of clauses        :   97 ( 661 expanded)
%              Number of leaves         :   13 ( 625 expanded)
%              Depth                    :   23
%              Number of atoms          :  627 (14631 expanded)
%              Number of equality atoms :  229 (2589 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f52,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
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

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
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
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_634,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_459,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_460,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_624,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_460])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_454,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_455,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_625,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1086,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_634,c_624,c_625])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_636,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1062,plain,
    ( k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47
    | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_2029,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1062])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1064,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1089,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1064,c_624,c_625])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_632,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1065,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1083,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1065,c_624,c_625])).

cnf(c_2260,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2029,c_26,c_29,c_1089,c_1083])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_245,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_246,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_647,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_630])).

cnf(c_1067,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_1239,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1067,c_624,c_625])).

cnf(c_646,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_630])).

cnf(c_1068,plain,
    ( v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_1130,plain,
    ( v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1068,c_624,c_625])).

cnf(c_1245,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1239,c_1130])).

cnf(c_2263,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2260,c_1245])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_643,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | v2_funct_1(k2_funct_1(X0_49))
    | ~ v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_684,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(k2_funct_1(X0_49)) = iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_686,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_642,plain,
    ( ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49))
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_687,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_689,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_relat_1(X1_49)
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_49)
    | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1410,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_644,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1434,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_1435,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_638,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | v1_funct_2(k2_funct_1(X0_49),X1_47,X0_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1060,plain,
    ( k2_relset_1(X0_47,X1_47,X0_49) != X1_47
    | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | v1_funct_2(k2_funct_1(X0_49),X1_47,X0_47) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1866,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1060])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_639,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | m1_subset_1(k2_funct_1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47)))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1059,plain,
    ( k2_relset_1(X0_47,X1_47,X0_49) != X1_47
    | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2060,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1059])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_312,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_20])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_406,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_22])).

cnf(c_407,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_1071,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_1213,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1071,c_624,c_625])).

cnf(c_1603,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1213])).

cnf(c_1266,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_1634,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1603,c_26,c_29,c_1086,c_1266,c_1089,c_1083])).

cnf(c_2265,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2260,c_1634])).

cnf(c_2364,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1062])).

cnf(c_631,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1066,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_640,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1058,plain,
    ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_1774,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1058])).

cnf(c_694,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_2173,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1774,c_19,c_17,c_15,c_694,c_1409,c_1434])).

cnf(c_2377,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2364,c_2173])).

cnf(c_3012,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2263,c_26,c_28,c_29,c_686,c_689,c_1089,c_1083,c_1410,c_1435,c_1866,c_2060,c_2377])).

cnf(c_2866,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_26,c_28,c_29,c_686,c_689,c_1089,c_1083,c_1410,c_1435,c_1866,c_2060])).

cnf(c_3016,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3012,c_2866])).

cnf(c_3020,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3016,c_1066,c_1089,c_1083])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:19 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.54/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.00  
% 2.54/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.54/1.00  
% 2.54/1.00  ------  iProver source info
% 2.54/1.00  
% 2.54/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.54/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.54/1.00  git: non_committed_changes: false
% 2.54/1.00  git: last_make_outside_of_git: false
% 2.54/1.00  
% 2.54/1.00  ------ 
% 2.54/1.00  
% 2.54/1.00  ------ Input Options
% 2.54/1.00  
% 2.54/1.00  --out_options                           all
% 2.54/1.00  --tptp_safe_out                         true
% 2.54/1.00  --problem_path                          ""
% 2.54/1.00  --include_path                          ""
% 2.54/1.00  --clausifier                            res/vclausify_rel
% 2.54/1.00  --clausifier_options                    --mode clausify
% 2.54/1.00  --stdin                                 false
% 2.54/1.00  --stats_out                             all
% 2.54/1.00  
% 2.54/1.00  ------ General Options
% 2.54/1.00  
% 2.54/1.00  --fof                                   false
% 2.54/1.00  --time_out_real                         305.
% 2.54/1.00  --time_out_virtual                      -1.
% 2.54/1.00  --symbol_type_check                     false
% 2.54/1.00  --clausify_out                          false
% 2.54/1.00  --sig_cnt_out                           false
% 2.54/1.00  --trig_cnt_out                          false
% 2.54/1.00  --trig_cnt_out_tolerance                1.
% 2.54/1.00  --trig_cnt_out_sk_spl                   false
% 2.54/1.00  --abstr_cl_out                          false
% 2.54/1.00  
% 2.54/1.00  ------ Global Options
% 2.54/1.00  
% 2.54/1.00  --schedule                              default
% 2.54/1.00  --add_important_lit                     false
% 2.54/1.00  --prop_solver_per_cl                    1000
% 2.54/1.00  --min_unsat_core                        false
% 2.54/1.00  --soft_assumptions                      false
% 2.54/1.00  --soft_lemma_size                       3
% 2.54/1.00  --prop_impl_unit_size                   0
% 2.54/1.00  --prop_impl_unit                        []
% 2.54/1.00  --share_sel_clauses                     true
% 2.54/1.00  --reset_solvers                         false
% 2.54/1.00  --bc_imp_inh                            [conj_cone]
% 2.54/1.00  --conj_cone_tolerance                   3.
% 2.54/1.00  --extra_neg_conj                        none
% 2.54/1.00  --large_theory_mode                     true
% 2.54/1.00  --prolific_symb_bound                   200
% 2.54/1.00  --lt_threshold                          2000
% 2.54/1.00  --clause_weak_htbl                      true
% 2.54/1.00  --gc_record_bc_elim                     false
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing Options
% 2.54/1.00  
% 2.54/1.00  --preprocessing_flag                    true
% 2.54/1.00  --time_out_prep_mult                    0.1
% 2.54/1.00  --splitting_mode                        input
% 2.54/1.00  --splitting_grd                         true
% 2.54/1.00  --splitting_cvd                         false
% 2.54/1.00  --splitting_cvd_svl                     false
% 2.54/1.00  --splitting_nvd                         32
% 2.54/1.00  --sub_typing                            true
% 2.54/1.00  --prep_gs_sim                           true
% 2.54/1.00  --prep_unflatten                        true
% 2.54/1.00  --prep_res_sim                          true
% 2.54/1.00  --prep_upred                            true
% 2.54/1.00  --prep_sem_filter                       exhaustive
% 2.54/1.00  --prep_sem_filter_out                   false
% 2.54/1.00  --pred_elim                             true
% 2.54/1.00  --res_sim_input                         true
% 2.54/1.00  --eq_ax_congr_red                       true
% 2.54/1.00  --pure_diseq_elim                       true
% 2.54/1.00  --brand_transform                       false
% 2.54/1.00  --non_eq_to_eq                          false
% 2.54/1.00  --prep_def_merge                        true
% 2.54/1.00  --prep_def_merge_prop_impl              false
% 2.54/1.00  --prep_def_merge_mbd                    true
% 2.54/1.00  --prep_def_merge_tr_red                 false
% 2.54/1.00  --prep_def_merge_tr_cl                  false
% 2.54/1.00  --smt_preprocessing                     true
% 2.54/1.00  --smt_ac_axioms                         fast
% 2.54/1.00  --preprocessed_out                      false
% 2.54/1.00  --preprocessed_stats                    false
% 2.54/1.00  
% 2.54/1.00  ------ Abstraction refinement Options
% 2.54/1.00  
% 2.54/1.00  --abstr_ref                             []
% 2.54/1.00  --abstr_ref_prep                        false
% 2.54/1.00  --abstr_ref_until_sat                   false
% 2.54/1.00  --abstr_ref_sig_restrict                funpre
% 2.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/1.00  --abstr_ref_under                       []
% 2.54/1.00  
% 2.54/1.00  ------ SAT Options
% 2.54/1.00  
% 2.54/1.00  --sat_mode                              false
% 2.54/1.00  --sat_fm_restart_options                ""
% 2.54/1.00  --sat_gr_def                            false
% 2.54/1.00  --sat_epr_types                         true
% 2.54/1.00  --sat_non_cyclic_types                  false
% 2.54/1.00  --sat_finite_models                     false
% 2.54/1.00  --sat_fm_lemmas                         false
% 2.54/1.00  --sat_fm_prep                           false
% 2.54/1.00  --sat_fm_uc_incr                        true
% 2.54/1.00  --sat_out_model                         small
% 2.54/1.00  --sat_out_clauses                       false
% 2.54/1.00  
% 2.54/1.00  ------ QBF Options
% 2.54/1.00  
% 2.54/1.00  --qbf_mode                              false
% 2.54/1.00  --qbf_elim_univ                         false
% 2.54/1.00  --qbf_dom_inst                          none
% 2.54/1.00  --qbf_dom_pre_inst                      false
% 2.54/1.00  --qbf_sk_in                             false
% 2.54/1.00  --qbf_pred_elim                         true
% 2.54/1.00  --qbf_split                             512
% 2.54/1.00  
% 2.54/1.00  ------ BMC1 Options
% 2.54/1.00  
% 2.54/1.00  --bmc1_incremental                      false
% 2.54/1.00  --bmc1_axioms                           reachable_all
% 2.54/1.00  --bmc1_min_bound                        0
% 2.54/1.00  --bmc1_max_bound                        -1
% 2.54/1.00  --bmc1_max_bound_default                -1
% 2.54/1.00  --bmc1_symbol_reachability              true
% 2.54/1.00  --bmc1_property_lemmas                  false
% 2.54/1.00  --bmc1_k_induction                      false
% 2.54/1.00  --bmc1_non_equiv_states                 false
% 2.54/1.00  --bmc1_deadlock                         false
% 2.54/1.00  --bmc1_ucm                              false
% 2.54/1.00  --bmc1_add_unsat_core                   none
% 2.54/1.00  --bmc1_unsat_core_children              false
% 2.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/1.00  --bmc1_out_stat                         full
% 2.54/1.00  --bmc1_ground_init                      false
% 2.54/1.00  --bmc1_pre_inst_next_state              false
% 2.54/1.00  --bmc1_pre_inst_state                   false
% 2.54/1.00  --bmc1_pre_inst_reach_state             false
% 2.54/1.00  --bmc1_out_unsat_core                   false
% 2.54/1.00  --bmc1_aig_witness_out                  false
% 2.54/1.00  --bmc1_verbose                          false
% 2.54/1.00  --bmc1_dump_clauses_tptp                false
% 2.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.54/1.00  --bmc1_dump_file                        -
% 2.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.54/1.00  --bmc1_ucm_extend_mode                  1
% 2.54/1.00  --bmc1_ucm_init_mode                    2
% 2.54/1.00  --bmc1_ucm_cone_mode                    none
% 2.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.54/1.00  --bmc1_ucm_relax_model                  4
% 2.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/1.00  --bmc1_ucm_layered_model                none
% 2.54/1.00  --bmc1_ucm_max_lemma_size               10
% 2.54/1.00  
% 2.54/1.00  ------ AIG Options
% 2.54/1.00  
% 2.54/1.00  --aig_mode                              false
% 2.54/1.00  
% 2.54/1.00  ------ Instantiation Options
% 2.54/1.00  
% 2.54/1.00  --instantiation_flag                    true
% 2.54/1.00  --inst_sos_flag                         false
% 2.54/1.00  --inst_sos_phase                        true
% 2.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/1.00  --inst_lit_sel_side                     num_symb
% 2.54/1.00  --inst_solver_per_active                1400
% 2.54/1.00  --inst_solver_calls_frac                1.
% 2.54/1.00  --inst_passive_queue_type               priority_queues
% 2.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/1.00  --inst_passive_queues_freq              [25;2]
% 2.54/1.00  --inst_dismatching                      true
% 2.54/1.00  --inst_eager_unprocessed_to_passive     true
% 2.54/1.00  --inst_prop_sim_given                   true
% 2.54/1.00  --inst_prop_sim_new                     false
% 2.54/1.00  --inst_subs_new                         false
% 2.54/1.00  --inst_eq_res_simp                      false
% 2.54/1.00  --inst_subs_given                       false
% 2.54/1.00  --inst_orphan_elimination               true
% 2.54/1.00  --inst_learning_loop_flag               true
% 2.54/1.00  --inst_learning_start                   3000
% 2.54/1.00  --inst_learning_factor                  2
% 2.54/1.00  --inst_start_prop_sim_after_learn       3
% 2.54/1.00  --inst_sel_renew                        solver
% 2.54/1.00  --inst_lit_activity_flag                true
% 2.54/1.00  --inst_restr_to_given                   false
% 2.54/1.00  --inst_activity_threshold               500
% 2.54/1.00  --inst_out_proof                        true
% 2.54/1.00  
% 2.54/1.00  ------ Resolution Options
% 2.54/1.00  
% 2.54/1.00  --resolution_flag                       true
% 2.54/1.00  --res_lit_sel                           adaptive
% 2.54/1.00  --res_lit_sel_side                      none
% 2.54/1.00  --res_ordering                          kbo
% 2.54/1.00  --res_to_prop_solver                    active
% 2.54/1.00  --res_prop_simpl_new                    false
% 2.54/1.00  --res_prop_simpl_given                  true
% 2.54/1.00  --res_passive_queue_type                priority_queues
% 2.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/1.00  --res_passive_queues_freq               [15;5]
% 2.54/1.00  --res_forward_subs                      full
% 2.54/1.00  --res_backward_subs                     full
% 2.54/1.00  --res_forward_subs_resolution           true
% 2.54/1.00  --res_backward_subs_resolution          true
% 2.54/1.00  --res_orphan_elimination                true
% 2.54/1.00  --res_time_limit                        2.
% 2.54/1.00  --res_out_proof                         true
% 2.54/1.00  
% 2.54/1.00  ------ Superposition Options
% 2.54/1.00  
% 2.54/1.00  --superposition_flag                    true
% 2.54/1.00  --sup_passive_queue_type                priority_queues
% 2.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.54/1.00  --demod_completeness_check              fast
% 2.54/1.00  --demod_use_ground                      true
% 2.54/1.00  --sup_to_prop_solver                    passive
% 2.54/1.00  --sup_prop_simpl_new                    true
% 2.54/1.00  --sup_prop_simpl_given                  true
% 2.54/1.00  --sup_fun_splitting                     false
% 2.54/1.00  --sup_smt_interval                      50000
% 2.54/1.00  
% 2.54/1.00  ------ Superposition Simplification Setup
% 2.54/1.00  
% 2.54/1.00  --sup_indices_passive                   []
% 2.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_full_bw                           [BwDemod]
% 2.54/1.00  --sup_immed_triv                        [TrivRules]
% 2.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_immed_bw_main                     []
% 2.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.00  
% 2.54/1.00  ------ Combination Options
% 2.54/1.00  
% 2.54/1.00  --comb_res_mult                         3
% 2.54/1.00  --comb_sup_mult                         2
% 2.54/1.00  --comb_inst_mult                        10
% 2.54/1.00  
% 2.54/1.00  ------ Debug Options
% 2.54/1.00  
% 2.54/1.00  --dbg_backtrace                         false
% 2.54/1.00  --dbg_dump_prop_clauses                 false
% 2.54/1.00  --dbg_dump_prop_clauses_file            -
% 2.54/1.00  --dbg_out_stat                          false
% 2.54/1.00  ------ Parsing...
% 2.54/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.54/1.00  ------ Proving...
% 2.54/1.00  ------ Problem Properties 
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  clauses                                 23
% 2.54/1.00  conjectures                             5
% 2.54/1.00  EPR                                     2
% 2.54/1.00  Horn                                    23
% 2.54/1.00  unary                                   8
% 2.54/1.00  binary                                  0
% 2.54/1.00  lits                                    84
% 2.54/1.00  lits eq                                 18
% 2.54/1.00  fd_pure                                 0
% 2.54/1.00  fd_pseudo                               0
% 2.54/1.00  fd_cond                                 0
% 2.54/1.00  fd_pseudo_cond                          0
% 2.54/1.00  AC symbols                              0
% 2.54/1.00  
% 2.54/1.00  ------ Schedule dynamic 5 is on 
% 2.54/1.00  
% 2.54/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  ------ 
% 2.54/1.00  Current options:
% 2.54/1.00  ------ 
% 2.54/1.00  
% 2.54/1.00  ------ Input Options
% 2.54/1.00  
% 2.54/1.00  --out_options                           all
% 2.54/1.00  --tptp_safe_out                         true
% 2.54/1.00  --problem_path                          ""
% 2.54/1.00  --include_path                          ""
% 2.54/1.00  --clausifier                            res/vclausify_rel
% 2.54/1.00  --clausifier_options                    --mode clausify
% 2.54/1.00  --stdin                                 false
% 2.54/1.00  --stats_out                             all
% 2.54/1.00  
% 2.54/1.00  ------ General Options
% 2.54/1.00  
% 2.54/1.00  --fof                                   false
% 2.54/1.00  --time_out_real                         305.
% 2.54/1.00  --time_out_virtual                      -1.
% 2.54/1.00  --symbol_type_check                     false
% 2.54/1.00  --clausify_out                          false
% 2.54/1.00  --sig_cnt_out                           false
% 2.54/1.00  --trig_cnt_out                          false
% 2.54/1.00  --trig_cnt_out_tolerance                1.
% 2.54/1.00  --trig_cnt_out_sk_spl                   false
% 2.54/1.00  --abstr_cl_out                          false
% 2.54/1.00  
% 2.54/1.00  ------ Global Options
% 2.54/1.00  
% 2.54/1.00  --schedule                              default
% 2.54/1.00  --add_important_lit                     false
% 2.54/1.00  --prop_solver_per_cl                    1000
% 2.54/1.00  --min_unsat_core                        false
% 2.54/1.00  --soft_assumptions                      false
% 2.54/1.00  --soft_lemma_size                       3
% 2.54/1.00  --prop_impl_unit_size                   0
% 2.54/1.00  --prop_impl_unit                        []
% 2.54/1.00  --share_sel_clauses                     true
% 2.54/1.00  --reset_solvers                         false
% 2.54/1.00  --bc_imp_inh                            [conj_cone]
% 2.54/1.00  --conj_cone_tolerance                   3.
% 2.54/1.00  --extra_neg_conj                        none
% 2.54/1.00  --large_theory_mode                     true
% 2.54/1.00  --prolific_symb_bound                   200
% 2.54/1.00  --lt_threshold                          2000
% 2.54/1.00  --clause_weak_htbl                      true
% 2.54/1.00  --gc_record_bc_elim                     false
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing Options
% 2.54/1.00  
% 2.54/1.00  --preprocessing_flag                    true
% 2.54/1.00  --time_out_prep_mult                    0.1
% 2.54/1.00  --splitting_mode                        input
% 2.54/1.00  --splitting_grd                         true
% 2.54/1.00  --splitting_cvd                         false
% 2.54/1.00  --splitting_cvd_svl                     false
% 2.54/1.00  --splitting_nvd                         32
% 2.54/1.00  --sub_typing                            true
% 2.54/1.00  --prep_gs_sim                           true
% 2.54/1.00  --prep_unflatten                        true
% 2.54/1.00  --prep_res_sim                          true
% 2.54/1.00  --prep_upred                            true
% 2.54/1.00  --prep_sem_filter                       exhaustive
% 2.54/1.00  --prep_sem_filter_out                   false
% 2.54/1.00  --pred_elim                             true
% 2.54/1.00  --res_sim_input                         true
% 2.54/1.00  --eq_ax_congr_red                       true
% 2.54/1.00  --pure_diseq_elim                       true
% 2.54/1.00  --brand_transform                       false
% 2.54/1.00  --non_eq_to_eq                          false
% 2.54/1.00  --prep_def_merge                        true
% 2.54/1.00  --prep_def_merge_prop_impl              false
% 2.54/1.00  --prep_def_merge_mbd                    true
% 2.54/1.00  --prep_def_merge_tr_red                 false
% 2.54/1.00  --prep_def_merge_tr_cl                  false
% 2.54/1.00  --smt_preprocessing                     true
% 2.54/1.00  --smt_ac_axioms                         fast
% 2.54/1.00  --preprocessed_out                      false
% 2.54/1.00  --preprocessed_stats                    false
% 2.54/1.00  
% 2.54/1.00  ------ Abstraction refinement Options
% 2.54/1.00  
% 2.54/1.00  --abstr_ref                             []
% 2.54/1.00  --abstr_ref_prep                        false
% 2.54/1.00  --abstr_ref_until_sat                   false
% 2.54/1.00  --abstr_ref_sig_restrict                funpre
% 2.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/1.00  --abstr_ref_under                       []
% 2.54/1.00  
% 2.54/1.00  ------ SAT Options
% 2.54/1.00  
% 2.54/1.00  --sat_mode                              false
% 2.54/1.00  --sat_fm_restart_options                ""
% 2.54/1.00  --sat_gr_def                            false
% 2.54/1.00  --sat_epr_types                         true
% 2.54/1.00  --sat_non_cyclic_types                  false
% 2.54/1.00  --sat_finite_models                     false
% 2.54/1.00  --sat_fm_lemmas                         false
% 2.54/1.00  --sat_fm_prep                           false
% 2.54/1.00  --sat_fm_uc_incr                        true
% 2.54/1.00  --sat_out_model                         small
% 2.54/1.00  --sat_out_clauses                       false
% 2.54/1.00  
% 2.54/1.00  ------ QBF Options
% 2.54/1.00  
% 2.54/1.00  --qbf_mode                              false
% 2.54/1.00  --qbf_elim_univ                         false
% 2.54/1.00  --qbf_dom_inst                          none
% 2.54/1.00  --qbf_dom_pre_inst                      false
% 2.54/1.00  --qbf_sk_in                             false
% 2.54/1.00  --qbf_pred_elim                         true
% 2.54/1.00  --qbf_split                             512
% 2.54/1.00  
% 2.54/1.00  ------ BMC1 Options
% 2.54/1.00  
% 2.54/1.00  --bmc1_incremental                      false
% 2.54/1.00  --bmc1_axioms                           reachable_all
% 2.54/1.00  --bmc1_min_bound                        0
% 2.54/1.00  --bmc1_max_bound                        -1
% 2.54/1.00  --bmc1_max_bound_default                -1
% 2.54/1.00  --bmc1_symbol_reachability              true
% 2.54/1.00  --bmc1_property_lemmas                  false
% 2.54/1.00  --bmc1_k_induction                      false
% 2.54/1.00  --bmc1_non_equiv_states                 false
% 2.54/1.00  --bmc1_deadlock                         false
% 2.54/1.00  --bmc1_ucm                              false
% 2.54/1.00  --bmc1_add_unsat_core                   none
% 2.54/1.00  --bmc1_unsat_core_children              false
% 2.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/1.00  --bmc1_out_stat                         full
% 2.54/1.00  --bmc1_ground_init                      false
% 2.54/1.00  --bmc1_pre_inst_next_state              false
% 2.54/1.00  --bmc1_pre_inst_state                   false
% 2.54/1.00  --bmc1_pre_inst_reach_state             false
% 2.54/1.00  --bmc1_out_unsat_core                   false
% 2.54/1.00  --bmc1_aig_witness_out                  false
% 2.54/1.00  --bmc1_verbose                          false
% 2.54/1.00  --bmc1_dump_clauses_tptp                false
% 2.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.54/1.00  --bmc1_dump_file                        -
% 2.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.54/1.00  --bmc1_ucm_extend_mode                  1
% 2.54/1.00  --bmc1_ucm_init_mode                    2
% 2.54/1.00  --bmc1_ucm_cone_mode                    none
% 2.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.54/1.00  --bmc1_ucm_relax_model                  4
% 2.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/1.00  --bmc1_ucm_layered_model                none
% 2.54/1.00  --bmc1_ucm_max_lemma_size               10
% 2.54/1.00  
% 2.54/1.00  ------ AIG Options
% 2.54/1.00  
% 2.54/1.00  --aig_mode                              false
% 2.54/1.00  
% 2.54/1.00  ------ Instantiation Options
% 2.54/1.00  
% 2.54/1.00  --instantiation_flag                    true
% 2.54/1.00  --inst_sos_flag                         false
% 2.54/1.00  --inst_sos_phase                        true
% 2.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/1.00  --inst_lit_sel_side                     none
% 2.54/1.00  --inst_solver_per_active                1400
% 2.54/1.00  --inst_solver_calls_frac                1.
% 2.54/1.00  --inst_passive_queue_type               priority_queues
% 2.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/1.00  --inst_passive_queues_freq              [25;2]
% 2.54/1.00  --inst_dismatching                      true
% 2.54/1.00  --inst_eager_unprocessed_to_passive     true
% 2.54/1.00  --inst_prop_sim_given                   true
% 2.54/1.00  --inst_prop_sim_new                     false
% 2.54/1.00  --inst_subs_new                         false
% 2.54/1.00  --inst_eq_res_simp                      false
% 2.54/1.00  --inst_subs_given                       false
% 2.54/1.00  --inst_orphan_elimination               true
% 2.54/1.00  --inst_learning_loop_flag               true
% 2.54/1.00  --inst_learning_start                   3000
% 2.54/1.00  --inst_learning_factor                  2
% 2.54/1.00  --inst_start_prop_sim_after_learn       3
% 2.54/1.00  --inst_sel_renew                        solver
% 2.54/1.00  --inst_lit_activity_flag                true
% 2.54/1.00  --inst_restr_to_given                   false
% 2.54/1.00  --inst_activity_threshold               500
% 2.54/1.00  --inst_out_proof                        true
% 2.54/1.00  
% 2.54/1.00  ------ Resolution Options
% 2.54/1.00  
% 2.54/1.00  --resolution_flag                       false
% 2.54/1.00  --res_lit_sel                           adaptive
% 2.54/1.00  --res_lit_sel_side                      none
% 2.54/1.00  --res_ordering                          kbo
% 2.54/1.00  --res_to_prop_solver                    active
% 2.54/1.00  --res_prop_simpl_new                    false
% 2.54/1.00  --res_prop_simpl_given                  true
% 2.54/1.00  --res_passive_queue_type                priority_queues
% 2.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/1.00  --res_passive_queues_freq               [15;5]
% 2.54/1.00  --res_forward_subs                      full
% 2.54/1.00  --res_backward_subs                     full
% 2.54/1.00  --res_forward_subs_resolution           true
% 2.54/1.00  --res_backward_subs_resolution          true
% 2.54/1.00  --res_orphan_elimination                true
% 2.54/1.00  --res_time_limit                        2.
% 2.54/1.00  --res_out_proof                         true
% 2.54/1.00  
% 2.54/1.00  ------ Superposition Options
% 2.54/1.00  
% 2.54/1.00  --superposition_flag                    true
% 2.54/1.00  --sup_passive_queue_type                priority_queues
% 2.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.54/1.00  --demod_completeness_check              fast
% 2.54/1.00  --demod_use_ground                      true
% 2.54/1.00  --sup_to_prop_solver                    passive
% 2.54/1.00  --sup_prop_simpl_new                    true
% 2.54/1.00  --sup_prop_simpl_given                  true
% 2.54/1.00  --sup_fun_splitting                     false
% 2.54/1.00  --sup_smt_interval                      50000
% 2.54/1.00  
% 2.54/1.00  ------ Superposition Simplification Setup
% 2.54/1.00  
% 2.54/1.00  --sup_indices_passive                   []
% 2.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_full_bw                           [BwDemod]
% 2.54/1.00  --sup_immed_triv                        [TrivRules]
% 2.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_immed_bw_main                     []
% 2.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.00  
% 2.54/1.00  ------ Combination Options
% 2.54/1.00  
% 2.54/1.00  --comb_res_mult                         3
% 2.54/1.00  --comb_sup_mult                         2
% 2.54/1.00  --comb_inst_mult                        10
% 2.54/1.00  
% 2.54/1.00  ------ Debug Options
% 2.54/1.00  
% 2.54/1.00  --dbg_backtrace                         false
% 2.54/1.00  --dbg_dump_prop_clauses                 false
% 2.54/1.00  --dbg_dump_prop_clauses_file            -
% 2.54/1.00  --dbg_out_stat                          false
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  ------ Proving...
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  % SZS status Theorem for theBenchmark.p
% 2.54/1.00  
% 2.54/1.00   Resolution empty clause
% 2.54/1.00  
% 2.54/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.54/1.00  
% 2.54/1.00  fof(f10,conjecture,(
% 2.54/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f11,negated_conjecture,(
% 2.54/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.54/1.00    inference(negated_conjecture,[],[f10])).
% 2.54/1.00  
% 2.54/1.00  fof(f26,plain,(
% 2.54/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.54/1.00    inference(ennf_transformation,[],[f11])).
% 2.54/1.00  
% 2.54/1.00  fof(f27,plain,(
% 2.54/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.54/1.00    inference(flattening,[],[f26])).
% 2.54/1.00  
% 2.54/1.00  fof(f30,plain,(
% 2.54/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.54/1.00    introduced(choice_axiom,[])).
% 2.54/1.00  
% 2.54/1.00  fof(f29,plain,(
% 2.54/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.54/1.00    introduced(choice_axiom,[])).
% 2.54/1.00  
% 2.54/1.00  fof(f28,plain,(
% 2.54/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.54/1.00    introduced(choice_axiom,[])).
% 2.54/1.00  
% 2.54/1.00  fof(f31,plain,(
% 2.54/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 2.54/1.00  
% 2.54/1.00  fof(f52,plain,(
% 2.54/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f7,axiom,(
% 2.54/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f21,plain,(
% 2.54/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.54/1.00    inference(ennf_transformation,[],[f7])).
% 2.54/1.00  
% 2.54/1.00  fof(f42,plain,(
% 2.54/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f21])).
% 2.54/1.00  
% 2.54/1.00  fof(f46,plain,(
% 2.54/1.00    l1_struct_0(sK0)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f48,plain,(
% 2.54/1.00    l1_struct_0(sK1)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f8,axiom,(
% 2.54/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f22,plain,(
% 2.54/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.54/1.00    inference(ennf_transformation,[],[f8])).
% 2.54/1.00  
% 2.54/1.00  fof(f23,plain,(
% 2.54/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.54/1.00    inference(flattening,[],[f22])).
% 2.54/1.00  
% 2.54/1.00  fof(f43,plain,(
% 2.54/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f23])).
% 2.54/1.00  
% 2.54/1.00  fof(f49,plain,(
% 2.54/1.00    v1_funct_1(sK2)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f53,plain,(
% 2.54/1.00    v2_funct_1(sK2)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f51,plain,(
% 2.54/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f50,plain,(
% 2.54/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f5,axiom,(
% 2.54/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f17,plain,(
% 2.54/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.54/1.00    inference(ennf_transformation,[],[f5])).
% 2.54/1.00  
% 2.54/1.00  fof(f18,plain,(
% 2.54/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.54/1.00    inference(flattening,[],[f17])).
% 2.54/1.00  
% 2.54/1.00  fof(f38,plain,(
% 2.54/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f18])).
% 2.54/1.00  
% 2.54/1.00  fof(f54,plain,(
% 2.54/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f3,axiom,(
% 2.54/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f13,plain,(
% 2.54/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.54/1.00    inference(ennf_transformation,[],[f3])).
% 2.54/1.00  
% 2.54/1.00  fof(f14,plain,(
% 2.54/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.54/1.00    inference(flattening,[],[f13])).
% 2.54/1.00  
% 2.54/1.00  fof(f36,plain,(
% 2.54/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f14])).
% 2.54/1.00  
% 2.54/1.00  fof(f35,plain,(
% 2.54/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f14])).
% 2.54/1.00  
% 2.54/1.00  fof(f1,axiom,(
% 2.54/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f12,plain,(
% 2.54/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.54/1.00    inference(ennf_transformation,[],[f1])).
% 2.54/1.00  
% 2.54/1.00  fof(f32,plain,(
% 2.54/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f12])).
% 2.54/1.00  
% 2.54/1.00  fof(f2,axiom,(
% 2.54/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f33,plain,(
% 2.54/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.54/1.00    inference(cnf_transformation,[],[f2])).
% 2.54/1.00  
% 2.54/1.00  fof(f6,axiom,(
% 2.54/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f19,plain,(
% 2.54/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.54/1.00    inference(ennf_transformation,[],[f6])).
% 2.54/1.00  
% 2.54/1.00  fof(f20,plain,(
% 2.54/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.54/1.00    inference(flattening,[],[f19])).
% 2.54/1.00  
% 2.54/1.00  fof(f40,plain,(
% 2.54/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f20])).
% 2.54/1.00  
% 2.54/1.00  fof(f41,plain,(
% 2.54/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f20])).
% 2.54/1.00  
% 2.54/1.00  fof(f9,axiom,(
% 2.54/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f24,plain,(
% 2.54/1.00    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.54/1.00    inference(ennf_transformation,[],[f9])).
% 2.54/1.00  
% 2.54/1.00  fof(f25,plain,(
% 2.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.54/1.00    inference(flattening,[],[f24])).
% 2.54/1.00  
% 2.54/1.00  fof(f45,plain,(
% 2.54/1.00    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f25])).
% 2.54/1.00  
% 2.54/1.00  fof(f47,plain,(
% 2.54/1.00    ~v2_struct_0(sK1)),
% 2.54/1.00    inference(cnf_transformation,[],[f31])).
% 2.54/1.00  
% 2.54/1.00  fof(f4,axiom,(
% 2.54/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.00  
% 2.54/1.00  fof(f15,plain,(
% 2.54/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.54/1.00    inference(ennf_transformation,[],[f4])).
% 2.54/1.00  
% 2.54/1.00  fof(f16,plain,(
% 2.54/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.54/1.00    inference(flattening,[],[f15])).
% 2.54/1.00  
% 2.54/1.00  fof(f37,plain,(
% 2.54/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/1.00    inference(cnf_transformation,[],[f16])).
% 2.54/1.00  
% 2.54/1.00  cnf(c_16,negated_conjecture,
% 2.54/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.54/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_634,negated_conjecture,
% 2.54/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_10,plain,
% 2.54/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.54/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_22,negated_conjecture,
% 2.54/1.00      ( l1_struct_0(sK0) ),
% 2.54/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_459,plain,
% 2.54/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.54/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_460,plain,
% 2.54/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.54/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_624,plain,
% 2.54/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_460]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_20,negated_conjecture,
% 2.54/1.00      ( l1_struct_0(sK1) ),
% 2.54/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_454,plain,
% 2.54/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.54/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_455,plain,
% 2.54/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.54/1.00      inference(unflattening,[status(thm)],[c_454]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_625,plain,
% 2.54/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_455]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1086,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_634,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_11,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.54/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_636,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
% 2.54/1.00      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1062,plain,
% 2.54/1.00      ( k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
% 2.54/1.00      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47
% 2.54/1.00      | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2029,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.54/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_1086,c_1062]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_19,negated_conjecture,
% 2.54/1.00      ( v1_funct_1(sK2) ),
% 2.54/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_26,plain,
% 2.54/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_15,negated_conjecture,
% 2.54/1.00      ( v2_funct_1(sK2) ),
% 2.54/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_29,plain,
% 2.54/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_17,negated_conjecture,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.54/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_633,negated_conjecture,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1064,plain,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1089,plain,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_1064,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_18,negated_conjecture,
% 2.54/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.54/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_632,negated_conjecture,
% 2.54/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1065,plain,
% 2.54/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1083,plain,
% 2.54/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_1065,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2260,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.54/1.00      inference(global_propositional_subsumption,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_2029,c_26,c_29,c_1089,c_1083]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_6,plain,
% 2.54/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.54/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.54/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.54/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.54/1.00      | ~ v1_funct_1(X3)
% 2.54/1.00      | ~ v1_funct_1(X2) ),
% 2.54/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_14,negated_conjecture,
% 2.54/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.54/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_245,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/1.00      | ~ v1_funct_2(X3,X1,X2)
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v1_funct_1(X3)
% 2.54/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 2.54/1.00      | u1_struct_0(sK1) != X2
% 2.54/1.00      | u1_struct_0(sK0) != X1
% 2.54/1.00      | sK2 != X3 ),
% 2.54/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_246,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.54/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.54/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_630,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.54/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_246]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_647,plain,
% 2.54/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.54/1.00      | sP0_iProver_split
% 2.54/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.54/1.00      inference(splitting,
% 2.54/1.00                [splitting(split),new_symbols(definition,[])],
% 2.54/1.00                [c_630]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1067,plain,
% 2.54/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.54/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.54/1.00      | sP0_iProver_split = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1239,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.54/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.54/1.00      | sP0_iProver_split = iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_1067,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_646,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ sP0_iProver_split ),
% 2.54/1.00      inference(splitting,
% 2.54/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.54/1.00                [c_630]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1068,plain,
% 2.54/1.00      ( v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | sP0_iProver_split != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1130,plain,
% 2.54/1.00      ( v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | sP0_iProver_split != iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_1068,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1245,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.54/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.54/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1239,c_1130]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2263,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.54/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.54/1.00      inference(demodulation,[status(thm)],[c_2260,c_1245]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_28,plain,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | v2_funct_1(k2_funct_1(X0))
% 2.54/1.00      | ~ v1_relat_1(X0) ),
% 2.54/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_643,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | v2_funct_1(k2_funct_1(X0_49))
% 2.54/1.00      | ~ v1_relat_1(X0_49) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_684,plain,
% 2.54/1.00      ( v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(k2_funct_1(X0_49)) = iProver_top
% 2.54/1.00      | v1_relat_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_686,plain,
% 2.54/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top
% 2.54/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_684]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_3,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0)
% 2.54/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | ~ v1_relat_1(X0) ),
% 2.54/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_642,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0_49)
% 2.54/1.00      | v1_funct_1(k2_funct_1(X0_49))
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | ~ v1_relat_1(X0_49) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_687,plain,
% 2.54/1.00      ( v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v1_relat_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_689,plain,
% 2.54/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top
% 2.54/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_687]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_0,plain,
% 2.54/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.54/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_645,plain,
% 2.54/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.54/1.00      | ~ v1_relat_1(X1_49)
% 2.54/1.00      | v1_relat_1(X0_49) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1321,plain,
% 2.54/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.54/1.00      | v1_relat_1(X0_49)
% 2.54/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1409,plain,
% 2.54/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.54/1.00      | v1_relat_1(sK2) ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_1321]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1410,plain,
% 2.54/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.54/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1,plain,
% 2.54/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.54/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_644,plain,
% 2.54/1.00      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1434,plain,
% 2.54/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_644]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1435,plain,
% 2.54/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_8,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.54/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_638,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.54/1.00      | v1_funct_2(k2_funct_1(X0_49),X1_47,X0_47)
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1060,plain,
% 2.54/1.00      ( k2_relset_1(X0_47,X1_47,X0_49) != X1_47
% 2.54/1.00      | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.54/1.00      | v1_funct_2(k2_funct_1(X0_49),X1_47,X0_47) = iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1866,plain,
% 2.54/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.54/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_1086,c_1060]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_7,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.54/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_639,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.54/1.00      | m1_subset_1(k2_funct_1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47)))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1059,plain,
% 2.54/1.00      ( k2_relset_1(X0_47,X1_47,X0_49) != X1_47
% 2.54/1.00      | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_funct_1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47))) = iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2060,plain,
% 2.54/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_1086,c_1059]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_12,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.54/1.00      | v2_struct_0(X2)
% 2.54/1.00      | ~ l1_struct_0(X1)
% 2.54/1.00      | ~ l1_struct_0(X2)
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.54/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_21,negated_conjecture,
% 2.54/1.00      ( ~ v2_struct_0(sK1) ),
% 2.54/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_311,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.54/1.00      | ~ l1_struct_0(X1)
% 2.54/1.00      | ~ l1_struct_0(X2)
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.54/1.00      | sK1 != X2 ),
% 2.54/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_312,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.54/1.00      | ~ l1_struct_0(X1)
% 2.54/1.00      | ~ l1_struct_0(sK1)
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.54/1.00      inference(unflattening,[status(thm)],[c_311]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_316,plain,
% 2.54/1.00      ( ~ l1_struct_0(X1)
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.54/1.00      inference(global_propositional_subsumption,[status(thm)],[c_312,c_20]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_317,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.54/1.00      | ~ l1_struct_0(X1)
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.54/1.00      inference(renaming,[status(thm)],[c_316]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_406,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 2.54/1.00      | sK0 != X1 ),
% 2.54/1.00      inference(resolution_lifted,[status(thm)],[c_317,c_22]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_407,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.54/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_627,plain,
% 2.54/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.54/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.54/1.00      | ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_407]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1071,plain,
% 2.54/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.54/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.54/1.00      | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1213,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.54/1.00      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.54/1.00      | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_1071,c_624,c_625]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1603,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.54/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_1086,c_1213]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1266,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.54/1.00      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.54/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_1213]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1634,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 2.54/1.00      inference(global_propositional_subsumption,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_1603,c_26,c_29,c_1086,c_1266,c_1089,c_1083]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2265,plain,
% 2.54/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.54/1.00      inference(demodulation,[status(thm)],[c_2260,c_1634]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2364,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.54/1.00      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.54/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_2265,c_1062]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_631,negated_conjecture,
% 2.54/1.00      ( v1_funct_1(sK2) ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1066,plain,
% 2.54/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_5,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0)
% 2.54/1.00      | ~ v2_funct_1(X0)
% 2.54/1.00      | ~ v1_relat_1(X0)
% 2.54/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.54/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_640,plain,
% 2.54/1.00      ( ~ v1_funct_1(X0_49)
% 2.54/1.00      | ~ v2_funct_1(X0_49)
% 2.54/1.00      | ~ v1_relat_1(X0_49)
% 2.54/1.00      | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
% 2.54/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1058,plain,
% 2.54/1.00      ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
% 2.54/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v2_funct_1(X0_49) != iProver_top
% 2.54/1.00      | v1_relat_1(X0_49) != iProver_top ),
% 2.54/1.00      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_1774,plain,
% 2.54/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.54/1.00      | v2_funct_1(sK2) != iProver_top
% 2.54/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.54/1.00      inference(superposition,[status(thm)],[c_1066,c_1058]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_694,plain,
% 2.54/1.00      ( ~ v1_funct_1(sK2)
% 2.54/1.00      | ~ v2_funct_1(sK2)
% 2.54/1.00      | ~ v1_relat_1(sK2)
% 2.54/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.54/1.00      inference(instantiation,[status(thm)],[c_640]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2173,plain,
% 2.54/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.54/1.00      inference(global_propositional_subsumption,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_1774,c_19,c_17,c_15,c_694,c_1409,c_1434]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2377,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.54/1.00      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.54/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_2364,c_2173]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_3012,plain,
% 2.54/1.00      ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.54/1.00      inference(global_propositional_subsumption,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_2263,c_26,c_28,c_29,c_686,c_689,c_1089,c_1083,c_1410,
% 2.54/1.00                 c_1435,c_1866,c_2060,c_2377]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_2866,plain,
% 2.54/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.54/1.00      inference(global_propositional_subsumption,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_2377,c_26,c_28,c_29,c_686,c_689,c_1089,c_1083,c_1410,
% 2.54/1.00                 c_1435,c_1866,c_2060]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_3016,plain,
% 2.54/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.54/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.54/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.54/1.00      inference(light_normalisation,[status(thm)],[c_3012,c_2866]) ).
% 2.54/1.00  
% 2.54/1.00  cnf(c_3020,plain,
% 2.54/1.00      ( $false ),
% 2.54/1.00      inference(forward_subsumption_resolution,
% 2.54/1.00                [status(thm)],
% 2.54/1.00                [c_3016,c_1066,c_1089,c_1083]) ).
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.54/1.00  
% 2.54/1.00  ------                               Statistics
% 2.54/1.00  
% 2.54/1.00  ------ General
% 2.54/1.00  
% 2.54/1.00  abstr_ref_over_cycles:                  0
% 2.54/1.00  abstr_ref_under_cycles:                 0
% 2.54/1.00  gc_basic_clause_elim:                   0
% 2.54/1.00  forced_gc_time:                         0
% 2.54/1.00  parsing_time:                           0.009
% 2.54/1.00  unif_index_cands_time:                  0.
% 2.54/1.00  unif_index_add_time:                    0.
% 2.54/1.00  orderings_time:                         0.
% 2.54/1.00  out_proof_time:                         0.03
% 2.54/1.00  total_time:                             0.208
% 2.54/1.00  num_of_symbols:                         52
% 2.54/1.00  num_of_terms:                           2808
% 2.54/1.00  
% 2.54/1.00  ------ Preprocessing
% 2.54/1.00  
% 2.54/1.00  num_of_splits:                          1
% 2.54/1.00  num_of_split_atoms:                     1
% 2.54/1.00  num_of_reused_defs:                     0
% 2.54/1.00  num_eq_ax_congr_red:                    2
% 2.54/1.00  num_of_sem_filtered_clauses:            2
% 2.54/1.00  num_of_subtypes:                        4
% 2.54/1.00  monotx_restored_types:                  0
% 2.54/1.00  sat_num_of_epr_types:                   0
% 2.54/1.00  sat_num_of_non_cyclic_types:            0
% 2.54/1.00  sat_guarded_non_collapsed_types:        1
% 2.54/1.00  num_pure_diseq_elim:                    0
% 2.54/1.00  simp_replaced_by:                       0
% 2.54/1.00  res_preprocessed:                       123
% 2.54/1.00  prep_upred:                             0
% 2.54/1.00  prep_unflattend:                        11
% 2.54/1.00  smt_new_axioms:                         0
% 2.54/1.00  pred_elim_cands:                        5
% 2.54/1.00  pred_elim:                              3
% 2.54/1.00  pred_elim_cl:                           1
% 2.54/1.00  pred_elim_cycles:                       5
% 2.54/1.00  merged_defs:                            0
% 2.54/1.00  merged_defs_ncl:                        0
% 2.54/1.00  bin_hyper_res:                          0
% 2.54/1.00  prep_cycles:                            4
% 2.54/1.00  pred_elim_time:                         0.007
% 2.54/1.00  splitting_time:                         0.
% 2.54/1.00  sem_filter_time:                        0.
% 2.54/1.00  monotx_time:                            0.
% 2.54/1.00  subtype_inf_time:                       0.
% 2.54/1.00  
% 2.54/1.00  ------ Problem properties
% 2.54/1.00  
% 2.54/1.00  clauses:                                23
% 2.54/1.00  conjectures:                            5
% 2.54/1.00  epr:                                    2
% 2.54/1.00  horn:                                   23
% 2.54/1.00  ground:                                 8
% 2.54/1.00  unary:                                  8
% 2.54/1.00  binary:                                 0
% 2.54/1.00  lits:                                   84
% 2.54/1.00  lits_eq:                                18
% 2.54/1.00  fd_pure:                                0
% 2.54/1.00  fd_pseudo:                              0
% 2.54/1.00  fd_cond:                                0
% 2.54/1.00  fd_pseudo_cond:                         0
% 2.54/1.00  ac_symbols:                             0
% 2.54/1.00  
% 2.54/1.00  ------ Propositional Solver
% 2.54/1.00  
% 2.54/1.00  prop_solver_calls:                      28
% 2.54/1.00  prop_fast_solver_calls:                 1097
% 2.54/1.00  smt_solver_calls:                       0
% 2.54/1.00  smt_fast_solver_calls:                  0
% 2.54/1.00  prop_num_of_clauses:                    987
% 2.54/1.00  prop_preprocess_simplified:             3894
% 2.54/1.00  prop_fo_subsumed:                       52
% 2.54/1.00  prop_solver_time:                       0.
% 2.54/1.00  smt_solver_time:                        0.
% 2.54/1.00  smt_fast_solver_time:                   0.
% 2.54/1.00  prop_fast_solver_time:                  0.
% 2.54/1.00  prop_unsat_core_time:                   0.
% 2.54/1.00  
% 2.54/1.00  ------ QBF
% 2.54/1.00  
% 2.54/1.00  qbf_q_res:                              0
% 2.54/1.00  qbf_num_tautologies:                    0
% 2.54/1.00  qbf_prep_cycles:                        0
% 2.54/1.00  
% 2.54/1.00  ------ BMC1
% 2.54/1.00  
% 2.54/1.00  bmc1_current_bound:                     -1
% 2.54/1.00  bmc1_last_solved_bound:                 -1
% 2.54/1.00  bmc1_unsat_core_size:                   -1
% 2.54/1.00  bmc1_unsat_core_parents_size:           -1
% 2.54/1.00  bmc1_merge_next_fun:                    0
% 2.54/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.54/1.00  
% 2.54/1.00  ------ Instantiation
% 2.54/1.00  
% 2.54/1.00  inst_num_of_clauses:                    325
% 2.54/1.00  inst_num_in_passive:                    57
% 2.54/1.00  inst_num_in_active:                     194
% 2.54/1.00  inst_num_in_unprocessed:                74
% 2.54/1.00  inst_num_of_loops:                      210
% 2.54/1.00  inst_num_of_learning_restarts:          0
% 2.54/1.00  inst_num_moves_active_passive:          12
% 2.54/1.00  inst_lit_activity:                      0
% 2.54/1.00  inst_lit_activity_moves:                0
% 2.54/1.00  inst_num_tautologies:                   0
% 2.54/1.00  inst_num_prop_implied:                  0
% 2.54/1.00  inst_num_existing_simplified:           0
% 2.54/1.00  inst_num_eq_res_simplified:             0
% 2.54/1.00  inst_num_child_elim:                    0
% 2.54/1.00  inst_num_of_dismatching_blockings:      64
% 2.54/1.00  inst_num_of_non_proper_insts:           307
% 2.54/1.00  inst_num_of_duplicates:                 0
% 2.54/1.00  inst_inst_num_from_inst_to_res:         0
% 2.54/1.00  inst_dismatching_checking_time:         0.
% 2.54/1.00  
% 2.54/1.00  ------ Resolution
% 2.54/1.00  
% 2.54/1.00  res_num_of_clauses:                     0
% 2.54/1.00  res_num_in_passive:                     0
% 2.54/1.00  res_num_in_active:                      0
% 2.54/1.00  res_num_of_loops:                       127
% 2.54/1.00  res_forward_subset_subsumed:            44
% 2.54/1.00  res_backward_subset_subsumed:           0
% 2.54/1.00  res_forward_subsumed:                   0
% 2.54/1.00  res_backward_subsumed:                  0
% 2.54/1.00  res_forward_subsumption_resolution:     0
% 2.54/1.00  res_backward_subsumption_resolution:    0
% 2.54/1.00  res_clause_to_clause_subsumption:       124
% 2.54/1.00  res_orphan_elimination:                 0
% 2.54/1.00  res_tautology_del:                      34
% 2.54/1.00  res_num_eq_res_simplified:              0
% 2.54/1.00  res_num_sel_changes:                    0
% 2.54/1.00  res_moves_from_active_to_pass:          0
% 2.54/1.00  
% 2.54/1.00  ------ Superposition
% 2.54/1.00  
% 2.54/1.00  sup_time_total:                         0.
% 2.54/1.00  sup_time_generating:                    0.
% 2.54/1.00  sup_time_sim_full:                      0.
% 2.54/1.00  sup_time_sim_immed:                     0.
% 2.54/1.00  
% 2.54/1.00  sup_num_of_clauses:                     41
% 2.54/1.00  sup_num_in_active:                      37
% 2.54/1.00  sup_num_in_passive:                     4
% 2.54/1.00  sup_num_of_loops:                       40
% 2.54/1.00  sup_fw_superposition:                   27
% 2.54/1.00  sup_bw_superposition:                   9
% 2.54/1.00  sup_immediate_simplified:               18
% 2.54/1.00  sup_given_eliminated:                   0
% 2.54/1.00  comparisons_done:                       0
% 2.54/1.00  comparisons_avoided:                    0
% 2.54/1.00  
% 2.54/1.00  ------ Simplifications
% 2.54/1.00  
% 2.54/1.00  
% 2.54/1.00  sim_fw_subset_subsumed:                 3
% 2.54/1.00  sim_bw_subset_subsumed:                 0
% 2.54/1.00  sim_fw_subsumed:                        3
% 2.54/1.00  sim_bw_subsumed:                        0
% 2.54/1.00  sim_fw_subsumption_res:                 4
% 2.54/1.00  sim_bw_subsumption_res:                 0
% 2.54/1.00  sim_tautology_del:                      0
% 2.54/1.00  sim_eq_tautology_del:                   11
% 2.54/1.00  sim_eq_res_simp:                        0
% 2.54/1.00  sim_fw_demodulated:                     0
% 2.54/1.00  sim_bw_demodulated:                     3
% 2.54/1.00  sim_light_normalised:                   25
% 2.54/1.00  sim_joinable_taut:                      0
% 2.54/1.00  sim_joinable_simp:                      0
% 2.54/1.00  sim_ac_normalised:                      0
% 2.54/1.00  sim_smt_subsumption:                    0
% 2.54/1.00  
%------------------------------------------------------------------------------
