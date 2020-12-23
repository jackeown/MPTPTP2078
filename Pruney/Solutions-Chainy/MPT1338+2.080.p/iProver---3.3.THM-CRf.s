%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:16 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  172 (1552 expanded)
%              Number of clauses        :  111 ( 501 expanded)
%              Number of leaves         :   16 ( 436 expanded)
%              Depth                    :   24
%              Number of atoms          :  552 (10798 expanded)
%              Number of equality atoms :  206 (3649 expanded)
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

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f43,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_705,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1026,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_287,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_288,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_702,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_282,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_283,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_703,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_283])).

cnf(c_1049,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1026,c_702,c_703])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1025,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1324,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1049,c_1025])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_706,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1046,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_706,c_702,c_703])).

cnf(c_1671,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1324,c_1046])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_389,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_390,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_22])).

cnf(c_395,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_701,plain,
    ( ~ v1_funct_2(sK2,X0_52,X1_52)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,sK2) != X1_52
    | k2_tops_2(X0_52,X1_52,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_1028,plain,
    ( k2_relset_1(X0_52,X1_52,sK2) != X1_52
    | k2_tops_2(X0_52,X1_52,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_52,X1_52) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1411,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1028])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_704,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1027,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1043,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1027,c_702,c_703])).

cnf(c_1438,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1411,c_1043,c_1049])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_707,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1097,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_707,c_702,c_703])).

cnf(c_1441,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1438,c_1097])).

cnf(c_1678,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1671,c_1441])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_462,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_22])).

cnf(c_467,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_699,plain,
    ( ~ v1_funct_2(sK2,X0_52,X1_52)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,sK2) != X1_52 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_1030,plain,
    ( k2_relset_1(X0_52,X1_52,sK2) != X1_52
    | v1_funct_2(sK2,X0_52,X1_52) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_1585,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1030])).

cnf(c_1791,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_1043,c_1049])).

cnf(c_1795,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1791,c_1671])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1024,plain,
    ( k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_1799,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1795,c_1024])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1022,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_1279,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1022])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_1262,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_710,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1272,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1273,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_1779,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_31,c_1262,c_1273])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_485,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_486,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_22])).

cnf(c_698,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1031,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_1785,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1779,c_1031])).

cnf(c_2384,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1799,c_1785])).

cnf(c_2607,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_2384])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_269,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_270,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_37,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_272,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_24,c_23,c_37])).

cnf(c_294,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_272])).

cnf(c_295,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_356,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_295,c_10])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_372,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_356,c_4])).

cnf(c_539,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_372,c_22])).

cnf(c_540,plain,
    ( ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_696,plain,
    ( ~ v1_funct_2(sK2,X0_52,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = X0_52 ),
    inference(subtyping,[status(esa)],[c_540])).

cnf(c_1033,plain,
    ( k1_relat_1(sK2) = X0_52
    | v1_funct_2(sK2,X0_52,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_1080,plain,
    ( k1_relat_1(sK2) = X0_52
    | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1033,c_703])).

cnf(c_1351,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
    | k1_relat_1(sK2) = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1080,c_31,c_1262,c_1273])).

cnf(c_1352,plain,
    ( k1_relat_1(sK2) = X0_52
    | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1351])).

cnf(c_1360,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1352])).

cnf(c_2512,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_1043])).

cnf(c_2609,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2607,c_2512])).

cnf(c_1798,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1795,c_1025])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_499,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_500,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_502,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_22])).

cnf(c_697,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_1032,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_1784,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1779,c_1032])).

cnf(c_2297,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1798,c_1784])).

cnf(c_2517,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2512,c_2297])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2609,c_2517])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.19/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.00  
% 2.19/1.00  ------  iProver source info
% 2.19/1.00  
% 2.19/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.00  git: non_committed_changes: false
% 2.19/1.00  git: last_make_outside_of_git: false
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     num_symb
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       true
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  ------ Parsing...
% 2.19/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.00  ------ Proving...
% 2.19/1.00  ------ Problem Properties 
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  clauses                                 19
% 2.19/1.00  conjectures                             4
% 2.19/1.00  EPR                                     0
% 2.19/1.00  Horn                                    18
% 2.19/1.00  unary                                   6
% 2.19/1.00  binary                                  5
% 2.19/1.00  lits                                    46
% 2.19/1.00  lits eq                                 16
% 2.19/1.00  fd_pure                                 0
% 2.19/1.00  fd_pseudo                               0
% 2.19/1.00  fd_cond                                 2
% 2.19/1.00  fd_pseudo_cond                          0
% 2.19/1.00  AC symbols                              0
% 2.19/1.00  
% 2.19/1.00  ------ Schedule dynamic 5 is on 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  Current options:
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     none
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       false
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ Proving...
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  % SZS status Theorem for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  fof(f13,conjecture,(
% 2.19/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f14,negated_conjecture,(
% 2.19/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.19/1.00    inference(negated_conjecture,[],[f13])).
% 2.19/1.00  
% 2.19/1.00  fof(f33,plain,(
% 2.19/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.19/1.00    inference(ennf_transformation,[],[f14])).
% 2.19/1.00  
% 2.19/1.00  fof(f34,plain,(
% 2.19/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.19/1.00    inference(flattening,[],[f33])).
% 2.19/1.00  
% 2.19/1.00  fof(f38,plain,(
% 2.19/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f37,plain,(
% 2.19/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f36,plain,(
% 2.19/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f39,plain,(
% 2.19/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.19/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).
% 2.19/1.00  
% 2.19/1.00  fof(f62,plain,(
% 2.19/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f10,axiom,(
% 2.19/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f28,plain,(
% 2.19/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.19/1.00    inference(ennf_transformation,[],[f10])).
% 2.19/1.00  
% 2.19/1.00  fof(f54,plain,(
% 2.19/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f28])).
% 2.19/1.00  
% 2.19/1.00  fof(f57,plain,(
% 2.19/1.00    l1_struct_0(sK0)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f59,plain,(
% 2.19/1.00    l1_struct_0(sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f6,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f21,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.00    inference(ennf_transformation,[],[f6])).
% 2.19/1.00  
% 2.19/1.00  fof(f46,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f21])).
% 2.19/1.00  
% 2.19/1.00  fof(f63,plain,(
% 2.19/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f12,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f31,plain,(
% 2.19/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/1.00    inference(ennf_transformation,[],[f12])).
% 2.19/1.00  
% 2.19/1.00  fof(f32,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/1.00    inference(flattening,[],[f31])).
% 2.19/1.00  
% 2.19/1.00  fof(f56,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f32])).
% 2.19/1.00  
% 2.19/1.00  fof(f64,plain,(
% 2.19/1.00    v2_funct_1(sK2)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f60,plain,(
% 2.19/1.00    v1_funct_1(sK2)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f61,plain,(
% 2.19/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f65,plain,(
% 2.19/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f9,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f26,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/1.00    inference(ennf_transformation,[],[f9])).
% 2.19/1.00  
% 2.19/1.00  fof(f27,plain,(
% 2.19/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/1.00    inference(flattening,[],[f26])).
% 2.19/1.00  
% 2.19/1.00  fof(f53,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f27])).
% 2.19/1.00  
% 2.19/1.00  fof(f5,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f20,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.00    inference(ennf_transformation,[],[f5])).
% 2.19/1.00  
% 2.19/1.00  fof(f45,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f20])).
% 2.19/1.00  
% 2.19/1.00  fof(f1,axiom,(
% 2.19/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f16,plain,(
% 2.19/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.19/1.00    inference(ennf_transformation,[],[f1])).
% 2.19/1.00  
% 2.19/1.00  fof(f40,plain,(
% 2.19/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f16])).
% 2.19/1.00  
% 2.19/1.00  fof(f2,axiom,(
% 2.19/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f41,plain,(
% 2.19/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f2])).
% 2.19/1.00  
% 2.19/1.00  fof(f3,axiom,(
% 2.19/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f17,plain,(
% 2.19/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/1.00    inference(ennf_transformation,[],[f3])).
% 2.19/1.00  
% 2.19/1.00  fof(f18,plain,(
% 2.19/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/1.00    inference(flattening,[],[f17])).
% 2.19/1.00  
% 2.19/1.00  fof(f42,plain,(
% 2.19/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f18])).
% 2.19/1.00  
% 2.19/1.00  fof(f7,axiom,(
% 2.19/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f22,plain,(
% 2.19/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.19/1.00    inference(ennf_transformation,[],[f7])).
% 2.19/1.00  
% 2.19/1.00  fof(f23,plain,(
% 2.19/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.19/1.00    inference(flattening,[],[f22])).
% 2.19/1.00  
% 2.19/1.00  fof(f48,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f23])).
% 2.19/1.00  
% 2.19/1.00  fof(f11,axiom,(
% 2.19/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f29,plain,(
% 2.19/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.19/1.00    inference(ennf_transformation,[],[f11])).
% 2.19/1.00  
% 2.19/1.00  fof(f30,plain,(
% 2.19/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.19/1.00    inference(flattening,[],[f29])).
% 2.19/1.00  
% 2.19/1.00  fof(f55,plain,(
% 2.19/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f30])).
% 2.19/1.00  
% 2.19/1.00  fof(f58,plain,(
% 2.19/1.00    ~v2_struct_0(sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f8,axiom,(
% 2.19/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f24,plain,(
% 2.19/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.19/1.00    inference(ennf_transformation,[],[f8])).
% 2.19/1.00  
% 2.19/1.00  fof(f25,plain,(
% 2.19/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.19/1.00    inference(flattening,[],[f24])).
% 2.19/1.00  
% 2.19/1.00  fof(f35,plain,(
% 2.19/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.19/1.00    inference(nnf_transformation,[],[f25])).
% 2.19/1.00  
% 2.19/1.00  fof(f49,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f35])).
% 2.19/1.00  
% 2.19/1.00  fof(f4,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f15,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.19/1.00    inference(pure_predicate_removal,[],[f4])).
% 2.19/1.00  
% 2.19/1.00  fof(f19,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.00    inference(ennf_transformation,[],[f15])).
% 2.19/1.00  
% 2.19/1.00  fof(f44,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f19])).
% 2.19/1.00  
% 2.19/1.00  fof(f43,plain,(
% 2.19/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f18])).
% 2.19/1.00  
% 2.19/1.00  cnf(c_20,negated_conjecture,
% 2.19/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.19/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_705,negated_conjecture,
% 2.19/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1026,plain,
% 2.19/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_14,plain,
% 2.19/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_25,negated_conjecture,
% 2.19/1.00      ( l1_struct_0(sK0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_287,plain,
% 2.19/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_288,plain,
% 2.19/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_287]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_702,plain,
% 2.19/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_288]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_23,negated_conjecture,
% 2.19/1.00      ( l1_struct_0(sK1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_282,plain,
% 2.19/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_283,plain,
% 2.19/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_282]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_703,plain,
% 2.19/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_283]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1049,plain,
% 2.19/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.19/1.00      inference(light_normalisation,[status(thm)],[c_1026,c_702,c_703]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_6,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_708,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.19/1.00      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1025,plain,
% 2.19/1.00      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.19/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1324,plain,
% 2.19/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1049,c_1025]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_19,negated_conjecture,
% 2.19/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_706,negated_conjecture,
% 2.19/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1046,plain,
% 2.19/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/1.00      inference(light_normalisation,[status(thm)],[c_706,c_702,c_703]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1671,plain,
% 2.19/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.19/1.00      inference(demodulation,[status(thm)],[c_1324,c_1046]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_16,plain,
% 2.19/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | ~ v2_funct_1(X0)
% 2.19/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.19/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_18,negated_conjecture,
% 2.19/1.00      ( v2_funct_1(sK2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_389,plain,
% 2.19/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.19/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.19/1.00      | sK2 != X0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_390,plain,
% 2.19/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.00      | ~ v1_funct_1(sK2)
% 2.19/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_22,negated_conjecture,
% 2.19/1.00      ( v1_funct_1(sK2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_394,plain,
% 2.19/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_390,c_22]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_395,plain,
% 2.19/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_394]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_701,plain,
% 2.19/1.00      ( ~ v1_funct_2(sK2,X0_52,X1_52)
% 2.19/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.19/1.00      | k2_relset_1(X0_52,X1_52,sK2) != X1_52
% 2.19/1.00      | k2_tops_2(X0_52,X1_52,sK2) = k2_funct_1(sK2) ),
% 2.19/1.00      inference(subtyping,[status(esa)],[c_395]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1028,plain,
% 2.19/1.00      ( k2_relset_1(X0_52,X1_52,sK2) != X1_52
% 2.19/1.00      | k2_tops_2(X0_52,X1_52,sK2) = k2_funct_1(sK2)
% 2.19/1.00      | v1_funct_2(sK2,X0_52,X1_52) != iProver_top
% 2.19/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1411,plain,
% 2.19/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.19/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1046,c_1028]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_21,negated_conjecture,
% 2.19/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.19/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_704,negated_conjecture,
% 2.19/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1027,plain,
% 2.19/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1043,plain,
% 2.19/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_1027,c_702,c_703]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1438,plain,
% 2.19/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1411,c_1043,c_1049]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_17,negated_conjecture,
% 2.19/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.19/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.19/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_707,negated_conjecture,
% 2.19/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.19/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1097,plain,
% 2.19/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.19/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_707,c_702,c_703]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1441,plain,
% 2.19/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.19/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.19/1.01      inference(demodulation,[status(thm)],[c_1438,c_1097]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1678,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.19/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.19/1.01      inference(demodulation,[status(thm)],[c_1671,c_1441]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_11,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.19/1.01      | ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v2_funct_1(X0)
% 2.19/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_461,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.19/1.01      | ~ v1_funct_1(X0)
% 2.19/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.19/1.01      | sK2 != X0 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_462,plain,
% 2.19/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.01      | ~ v1_funct_1(sK2)
% 2.19/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_466,plain,
% 2.19/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_462,c_22]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_467,plain,
% 2.19/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/1.01      inference(renaming,[status(thm)],[c_466]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_699,plain,
% 2.19/1.01      ( ~ v1_funct_2(sK2,X0_52,X1_52)
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.19/1.01      | k2_relset_1(X0_52,X1_52,sK2) != X1_52 ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_467]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1030,plain,
% 2.19/1.01      ( k2_relset_1(X0_52,X1_52,sK2) != X1_52
% 2.19/1.01      | v1_funct_2(sK2,X0_52,X1_52) != iProver_top
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1585,plain,
% 2.19/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1046,c_1030]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1791,plain,
% 2.19/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1585,c_1043,c_1049]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1795,plain,
% 2.19/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_1791,c_1671]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_5,plain,
% 2.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.19/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_709,plain,
% 2.19/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.19/1.01      | k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1024,plain,
% 2.19/1.01      ( k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51)
% 2.19/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1799,plain,
% 2.19/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1795,c_1024]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_0,plain,
% 2.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/1.01      | ~ v1_relat_1(X1)
% 2.19/1.01      | v1_relat_1(X0) ),
% 2.19/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_711,plain,
% 2.19/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.19/1.01      | ~ v1_relat_1(X1_51)
% 2.19/1.01      | v1_relat_1(X0_51) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1022,plain,
% 2.19/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 2.19/1.01      | v1_relat_1(X1_51) != iProver_top
% 2.19/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1279,plain,
% 2.19/1.01      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.19/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1049,c_1022]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_31,plain,
% 2.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1183,plain,
% 2.19/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.19/1.01      | v1_relat_1(X0_51)
% 2.19/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.19/1.01      inference(instantiation,[status(thm)],[c_711]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1261,plain,
% 2.19/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.19/1.01      | v1_relat_1(sK2) ),
% 2.19/1.01      inference(instantiation,[status(thm)],[c_1183]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1262,plain,
% 2.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.19/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1,plain,
% 2.19/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_710,plain,
% 2.19/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1272,plain,
% 2.19/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.19/1.01      inference(instantiation,[status(thm)],[c_710]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1273,plain,
% 2.19/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1779,plain,
% 2.19/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1279,c_31,c_1262,c_1273]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_3,plain,
% 2.19/1.01      ( ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v2_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.19/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_485,plain,
% 2.19/1.01      ( ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.19/1.01      | sK2 != X0 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_486,plain,
% 2.19/1.01      ( ~ v1_funct_1(sK2)
% 2.19/1.01      | ~ v1_relat_1(sK2)
% 2.19/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_485]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_488,plain,
% 2.19/1.01      ( ~ v1_relat_1(sK2)
% 2.19/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_486,c_22]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_698,plain,
% 2.19/1.01      ( ~ v1_relat_1(sK2)
% 2.19/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_488]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1031,plain,
% 2.19/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1785,plain,
% 2.19/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1779,c_1031]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2384,plain,
% 2.19/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_1799,c_1785]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2607,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1678,c_2384]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_7,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.01      | v1_partfun1(X0,X1)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.01      | v1_xboole_0(X2)
% 2.19/1.01      | ~ v1_funct_1(X0) ),
% 2.19/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_15,plain,
% 2.19/1.01      ( v2_struct_0(X0)
% 2.19/1.01      | ~ l1_struct_0(X0)
% 2.19/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.19/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_24,negated_conjecture,
% 2.19/1.01      ( ~ v2_struct_0(sK1) ),
% 2.19/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_269,plain,
% 2.19/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_270,plain,
% 2.19/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_269]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_37,plain,
% 2.19/1.01      ( v2_struct_0(sK1)
% 2.19/1.01      | ~ l1_struct_0(sK1)
% 2.19/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.19/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_272,plain,
% 2.19/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_270,c_24,c_23,c_37]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_294,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.01      | v1_partfun1(X0,X1)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.01      | ~ v1_funct_1(X0)
% 2.19/1.01      | u1_struct_0(sK1) != X2 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_272]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_295,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.19/1.01      | v1_partfun1(X0,X1)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_funct_1(X0) ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_294]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_10,plain,
% 2.19/1.01      ( ~ v1_partfun1(X0,X1)
% 2.19/1.01      | ~ v4_relat_1(X0,X1)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(X0) = X1 ),
% 2.19/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_356,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.19/1.01      | ~ v4_relat_1(X0,X1)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(X0) = X1 ),
% 2.19/1.01      inference(resolution,[status(thm)],[c_295,c_10]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_4,plain,
% 2.19/1.01      ( v4_relat_1(X0,X1)
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.19/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_372,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(X0) = X1 ),
% 2.19/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_356,c_4]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_539,plain,
% 2.19/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k1_relat_1(X0) = X1
% 2.19/1.01      | sK2 != X0 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_372,c_22]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_540,plain,
% 2.19/1.01      ( ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
% 2.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_relat_1(sK2)
% 2.19/1.01      | k1_relat_1(sK2) = X0 ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_539]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_696,plain,
% 2.19/1.01      ( ~ v1_funct_2(sK2,X0_52,u1_struct_0(sK1))
% 2.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
% 2.19/1.01      | ~ v1_relat_1(sK2)
% 2.19/1.01      | k1_relat_1(sK2) = X0_52 ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_540]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1033,plain,
% 2.19/1.01      ( k1_relat_1(sK2) = X0_52
% 2.19/1.01      | v1_funct_2(sK2,X0_52,u1_struct_0(sK1)) != iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
% 2.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1080,plain,
% 2.19/1.01      ( k1_relat_1(sK2) = X0_52
% 2.19/1.01      | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_1033,c_703]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1351,plain,
% 2.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.19/1.01      | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.19/1.01      | k1_relat_1(sK2) = X0_52 ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1080,c_31,c_1262,c_1273]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1352,plain,
% 2.19/1.01      ( k1_relat_1(sK2) = X0_52
% 2.19/1.01      | v1_funct_2(sK2,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top ),
% 2.19/1.01      inference(renaming,[status(thm)],[c_1351]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1360,plain,
% 2.19/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.19/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1049,c_1352]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2512,plain,
% 2.19/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_1360,c_1043]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2609,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_2607,c_2512]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1798,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1795,c_1025]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2,plain,
% 2.19/1.01      ( ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v2_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.19/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_499,plain,
% 2.19/1.01      ( ~ v1_funct_1(X0)
% 2.19/1.01      | ~ v1_relat_1(X0)
% 2.19/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.19/1.01      | sK2 != X0 ),
% 2.19/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_500,plain,
% 2.19/1.01      ( ~ v1_funct_1(sK2)
% 2.19/1.01      | ~ v1_relat_1(sK2)
% 2.19/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(unflattening,[status(thm)],[c_499]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_502,plain,
% 2.19/1.01      ( ~ v1_relat_1(sK2)
% 2.19/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(global_propositional_subsumption,
% 2.19/1.01                [status(thm)],
% 2.19/1.01                [c_500,c_22]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_697,plain,
% 2.19/1.01      ( ~ v1_relat_1(sK2)
% 2.19/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(subtyping,[status(esa)],[c_502]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1032,plain,
% 2.19/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.19/1.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_1784,plain,
% 2.19/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(superposition,[status(thm)],[c_1779,c_1032]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2297,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(light_normalisation,[status(thm)],[c_1798,c_1784]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(c_2517,plain,
% 2.19/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/1.01      inference(demodulation,[status(thm)],[c_2512,c_2297]) ).
% 2.19/1.01  
% 2.19/1.01  cnf(contradiction,plain,
% 2.19/1.01      ( $false ),
% 2.19/1.01      inference(minisat,[status(thm)],[c_2609,c_2517]) ).
% 2.19/1.01  
% 2.19/1.01  
% 2.19/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.01  
% 2.19/1.01  ------                               Statistics
% 2.19/1.01  
% 2.19/1.01  ------ General
% 2.19/1.01  
% 2.19/1.01  abstr_ref_over_cycles:                  0
% 2.19/1.01  abstr_ref_under_cycles:                 0
% 2.19/1.01  gc_basic_clause_elim:                   0
% 2.19/1.01  forced_gc_time:                         0
% 2.19/1.01  parsing_time:                           0.009
% 2.19/1.01  unif_index_cands_time:                  0.
% 2.19/1.01  unif_index_add_time:                    0.
% 2.19/1.01  orderings_time:                         0.
% 2.19/1.01  out_proof_time:                         0.013
% 2.19/1.01  total_time:                             0.134
% 2.19/1.01  num_of_symbols:                         57
% 2.19/1.01  num_of_terms:                           2349
% 2.19/1.01  
% 2.19/1.01  ------ Preprocessing
% 2.19/1.01  
% 2.19/1.01  num_of_splits:                          2
% 2.19/1.01  num_of_split_atoms:                     2
% 2.19/1.01  num_of_reused_defs:                     0
% 2.19/1.01  num_eq_ax_congr_red:                    5
% 2.19/1.01  num_of_sem_filtered_clauses:            1
% 2.19/1.01  num_of_subtypes:                        4
% 2.19/1.01  monotx_restored_types:                  1
% 2.19/1.01  sat_num_of_epr_types:                   0
% 2.19/1.01  sat_num_of_non_cyclic_types:            0
% 2.19/1.01  sat_guarded_non_collapsed_types:        0
% 2.19/1.01  num_pure_diseq_elim:                    0
% 2.19/1.01  simp_replaced_by:                       0
% 2.19/1.01  res_preprocessed:                       113
% 2.19/1.01  prep_upred:                             0
% 2.19/1.01  prep_unflattend:                        16
% 2.19/1.01  smt_new_axioms:                         0
% 2.19/1.01  pred_elim_cands:                        3
% 2.19/1.01  pred_elim:                              7
% 2.19/1.01  pred_elim_cl:                           8
% 2.19/1.01  pred_elim_cycles:                       10
% 2.19/1.01  merged_defs:                            0
% 2.19/1.01  merged_defs_ncl:                        0
% 2.19/1.01  bin_hyper_res:                          0
% 2.19/1.01  prep_cycles:                            4
% 2.19/1.01  pred_elim_time:                         0.007
% 2.19/1.01  splitting_time:                         0.
% 2.19/1.01  sem_filter_time:                        0.
% 2.19/1.01  monotx_time:                            0.
% 2.19/1.01  subtype_inf_time:                       0.001
% 2.19/1.01  
% 2.19/1.01  ------ Problem properties
% 2.19/1.01  
% 2.19/1.01  clauses:                                19
% 2.19/1.01  conjectures:                            4
% 2.19/1.01  epr:                                    0
% 2.19/1.01  horn:                                   18
% 2.19/1.01  ground:                                 9
% 2.19/1.01  unary:                                  6
% 2.19/1.01  binary:                                 5
% 2.19/1.01  lits:                                   46
% 2.19/1.01  lits_eq:                                16
% 2.19/1.01  fd_pure:                                0
% 2.19/1.01  fd_pseudo:                              0
% 2.19/1.01  fd_cond:                                2
% 2.19/1.01  fd_pseudo_cond:                         0
% 2.19/1.01  ac_symbols:                             0
% 2.19/1.01  
% 2.19/1.01  ------ Propositional Solver
% 2.19/1.01  
% 2.19/1.01  prop_solver_calls:                      29
% 2.19/1.01  prop_fast_solver_calls:                 758
% 2.19/1.01  smt_solver_calls:                       0
% 2.19/1.01  smt_fast_solver_calls:                  0
% 2.19/1.01  prop_num_of_clauses:                    927
% 2.19/1.01  prop_preprocess_simplified:             3514
% 2.19/1.01  prop_fo_subsumed:                       19
% 2.19/1.01  prop_solver_time:                       0.
% 2.19/1.01  smt_solver_time:                        0.
% 2.19/1.01  smt_fast_solver_time:                   0.
% 2.19/1.01  prop_fast_solver_time:                  0.
% 2.19/1.01  prop_unsat_core_time:                   0.
% 2.19/1.01  
% 2.19/1.01  ------ QBF
% 2.19/1.01  
% 2.19/1.01  qbf_q_res:                              0
% 2.19/1.01  qbf_num_tautologies:                    0
% 2.19/1.01  qbf_prep_cycles:                        0
% 2.19/1.01  
% 2.19/1.01  ------ BMC1
% 2.19/1.01  
% 2.19/1.01  bmc1_current_bound:                     -1
% 2.19/1.01  bmc1_last_solved_bound:                 -1
% 2.19/1.01  bmc1_unsat_core_size:                   -1
% 2.19/1.01  bmc1_unsat_core_parents_size:           -1
% 2.19/1.01  bmc1_merge_next_fun:                    0
% 2.19/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.01  
% 2.19/1.01  ------ Instantiation
% 2.19/1.01  
% 2.19/1.01  inst_num_of_clauses:                    307
% 2.19/1.01  inst_num_in_passive:                    110
% 2.19/1.01  inst_num_in_active:                     188
% 2.19/1.01  inst_num_in_unprocessed:                9
% 2.19/1.01  inst_num_of_loops:                      210
% 2.19/1.01  inst_num_of_learning_restarts:          0
% 2.19/1.01  inst_num_moves_active_passive:          17
% 2.19/1.01  inst_lit_activity:                      0
% 2.19/1.01  inst_lit_activity_moves:                0
% 2.19/1.01  inst_num_tautologies:                   0
% 2.19/1.01  inst_num_prop_implied:                  0
% 2.19/1.01  inst_num_existing_simplified:           0
% 2.19/1.01  inst_num_eq_res_simplified:             0
% 2.19/1.01  inst_num_child_elim:                    0
% 2.19/1.01  inst_num_of_dismatching_blockings:      45
% 2.19/1.01  inst_num_of_non_proper_insts:           284
% 2.19/1.01  inst_num_of_duplicates:                 0
% 2.19/1.01  inst_inst_num_from_inst_to_res:         0
% 2.19/1.01  inst_dismatching_checking_time:         0.
% 2.19/1.01  
% 2.19/1.01  ------ Resolution
% 2.19/1.01  
% 2.19/1.01  res_num_of_clauses:                     0
% 2.19/1.01  res_num_in_passive:                     0
% 2.19/1.01  res_num_in_active:                      0
% 2.19/1.01  res_num_of_loops:                       117
% 2.19/1.01  res_forward_subset_subsumed:            50
% 2.19/1.01  res_backward_subset_subsumed:           0
% 2.19/1.01  res_forward_subsumed:                   0
% 2.19/1.01  res_backward_subsumed:                  0
% 2.19/1.01  res_forward_subsumption_resolution:     1
% 2.19/1.01  res_backward_subsumption_resolution:    0
% 2.19/1.01  res_clause_to_clause_subsumption:       58
% 2.19/1.01  res_orphan_elimination:                 0
% 2.19/1.01  res_tautology_del:                      35
% 2.19/1.01  res_num_eq_res_simplified:              0
% 2.19/1.01  res_num_sel_changes:                    0
% 2.19/1.01  res_moves_from_active_to_pass:          0
% 2.19/1.01  
% 2.19/1.01  ------ Superposition
% 2.19/1.01  
% 2.19/1.01  sup_time_total:                         0.
% 2.19/1.01  sup_time_generating:                    0.
% 2.19/1.01  sup_time_sim_full:                      0.
% 2.19/1.01  sup_time_sim_immed:                     0.
% 2.19/1.01  
% 2.19/1.01  sup_num_of_clauses:                     29
% 2.19/1.01  sup_num_in_active:                      17
% 2.19/1.01  sup_num_in_passive:                     12
% 2.19/1.01  sup_num_of_loops:                       41
% 2.19/1.01  sup_fw_superposition:                   8
% 2.19/1.01  sup_bw_superposition:                   14
% 2.19/1.01  sup_immediate_simplified:               7
% 2.19/1.01  sup_given_eliminated:                   0
% 2.19/1.01  comparisons_done:                       0
% 2.19/1.01  comparisons_avoided:                    0
% 2.19/1.01  
% 2.19/1.01  ------ Simplifications
% 2.19/1.01  
% 2.19/1.01  
% 2.19/1.01  sim_fw_subset_subsumed:                 7
% 2.19/1.01  sim_bw_subset_subsumed:                 2
% 2.19/1.01  sim_fw_subsumed:                        0
% 2.19/1.01  sim_bw_subsumed:                        0
% 2.19/1.01  sim_fw_subsumption_res:                 0
% 2.19/1.01  sim_bw_subsumption_res:                 0
% 2.19/1.01  sim_tautology_del:                      0
% 2.19/1.01  sim_eq_tautology_del:                   0
% 2.19/1.01  sim_eq_res_simp:                        0
% 2.19/1.01  sim_fw_demodulated:                     0
% 2.19/1.01  sim_bw_demodulated:                     22
% 2.19/1.01  sim_light_normalised:                   10
% 2.19/1.01  sim_joinable_taut:                      0
% 2.19/1.01  sim_joinable_simp:                      0
% 2.19/1.01  sim_ac_normalised:                      0
% 2.19/1.01  sim_smt_subsumption:                    0
% 2.19/1.01  
%------------------------------------------------------------------------------
