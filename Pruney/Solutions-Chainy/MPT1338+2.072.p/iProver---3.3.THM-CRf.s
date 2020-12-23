%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:14 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  171 (3140 expanded)
%              Number of clauses        :  107 (1019 expanded)
%              Number of leaves         :   17 ( 882 expanded)
%              Depth                    :   22
%              Number of atoms          :  518 (21533 expanded)
%              Number of equality atoms :  199 (7355 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39,f38])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f60,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

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
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_568,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_917,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_300,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_301,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_564,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_295,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_296,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_565,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_296])).

cnf(c_937,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_917,c_564,c_565])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_908,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_1171,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_908])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_578,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1187,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1188,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_1366,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1171,c_32,c_1176,c_1188])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_393,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_394,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_23])).

cnf(c_562,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_921,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1371,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1366,c_921])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_569,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_934,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_569,c_564,c_565])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_369,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_370,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_374,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_23])).

cnf(c_375,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_563,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_920,plain,
    ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_1285,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_920])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_567,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_918,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_931,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_918,c_564,c_565])).

cnf(c_1319,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1285,c_937,c_931])).

cnf(c_1420,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1371,c_1319])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_573,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_914,plain,
    ( v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_1596,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_914])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2714,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_30,c_937,c_931])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_913,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_1491,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_937,c_913])).

cnf(c_1738,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1491,c_934])).

cnf(c_1744,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1738,c_937])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_282,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_283,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_285,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_25,c_24,c_47])).

cnf(c_307,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_285])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_415,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_308,c_11])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_415,c_5])).

cnf(c_561,plain,
    ( ~ v1_funct_2(X0_52,X0_53,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k1_relat_1(X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_922,plain,
    ( k1_relat_1(X0_52) = X0_53
    | v1_funct_2(X0_52,X0_53,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_2165,plain,
    ( k1_relat_1(X0_52) = X0_53
    | v1_funct_2(X0_52,X0_53,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_922,c_1738])).

cnf(c_2175,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_2165])).

cnf(c_1745,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1738,c_931])).

cnf(c_2591,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2175,c_30,c_32,c_1176,c_1188,c_1745])).

cnf(c_2718,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2714,c_1738,c_2591])).

cnf(c_2722,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2718,c_913])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_577,plain,
    ( ~ v1_relat_1(X0_52)
    | k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_910,plain,
    ( k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1373,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1366,c_910])).

cnf(c_2733,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2722,c_1373])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_912,plain,
    ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_2723,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2718,c_912])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_576,plain,
    ( ~ v1_relat_1(X0_52)
    | k1_relat_1(k4_relat_1(X0_52)) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_911,plain,
    ( k1_relat_1(k4_relat_1(X0_52)) = k2_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_1372,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1366,c_911])).

cnf(c_2730,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2723,c_1372])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_570,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_974,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_570,c_564,c_565])).

cnf(c_1322,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1319,c_974])).

cnf(c_1419,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1371,c_1322])).

cnf(c_1741,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1738,c_1419])).

cnf(c_2594,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2591,c_1741])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2733,c_2730,c_2594])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:44:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.58/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.00  
% 2.58/1.00  ------  iProver source info
% 2.58/1.00  
% 2.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.00  git: non_committed_changes: false
% 2.58/1.00  git: last_make_outside_of_git: false
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     num_symb
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       true
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  ------ Parsing...
% 2.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.00  ------ Proving...
% 2.58/1.00  ------ Problem Properties 
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  clauses                                 19
% 2.58/1.00  conjectures                             5
% 2.58/1.00  EPR                                     1
% 2.58/1.00  Horn                                    19
% 2.58/1.00  unary                                   7
% 2.58/1.00  binary                                  6
% 2.58/1.00  lits                                    43
% 2.58/1.00  lits eq                                 13
% 2.58/1.00  fd_pure                                 0
% 2.58/1.00  fd_pseudo                               0
% 2.58/1.00  fd_cond                                 0
% 2.58/1.00  fd_pseudo_cond                          1
% 2.58/1.00  AC symbols                              0
% 2.58/1.00  
% 2.58/1.00  ------ Schedule dynamic 5 is on 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  Current options:
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     none
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       false
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ Proving...
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS status Theorem for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  fof(f14,conjecture,(
% 2.58/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f15,negated_conjecture,(
% 2.58/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.58/1.00    inference(negated_conjecture,[],[f14])).
% 2.58/1.00  
% 2.58/1.00  fof(f35,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f15])).
% 2.58/1.00  
% 2.58/1.00  fof(f36,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f35])).
% 2.58/1.00  
% 2.58/1.00  fof(f40,plain,(
% 2.58/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f39,plain,(
% 2.58/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f38,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f41,plain,(
% 2.58/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39,f38])).
% 2.58/1.00  
% 2.58/1.00  fof(f65,plain,(
% 2.58/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f10,axiom,(
% 2.58/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f28,plain,(
% 2.58/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f10])).
% 2.58/1.00  
% 2.58/1.00  fof(f54,plain,(
% 2.58/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f28])).
% 2.58/1.00  
% 2.58/1.00  fof(f60,plain,(
% 2.58/1.00    l1_struct_0(sK0)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f62,plain,(
% 2.58/1.00    l1_struct_0(sK1)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f1,axiom,(
% 2.58/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f17,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f1])).
% 2.58/1.00  
% 2.58/1.00  fof(f42,plain,(
% 2.58/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f17])).
% 2.58/1.00  
% 2.58/1.00  fof(f2,axiom,(
% 2.58/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f43,plain,(
% 2.58/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f2])).
% 2.58/1.00  
% 2.58/1.00  fof(f4,axiom,(
% 2.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f19,plain,(
% 2.58/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f4])).
% 2.58/1.00  
% 2.58/1.00  fof(f20,plain,(
% 2.58/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/1.00    inference(flattening,[],[f19])).
% 2.58/1.00  
% 2.58/1.00  fof(f46,plain,(
% 2.58/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f20])).
% 2.58/1.00  
% 2.58/1.00  fof(f67,plain,(
% 2.58/1.00    v2_funct_1(sK2)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f63,plain,(
% 2.58/1.00    v1_funct_1(sK2)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f66,plain,(
% 2.58/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f12,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f31,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/1.00    inference(ennf_transformation,[],[f12])).
% 2.58/1.00  
% 2.58/1.00  fof(f32,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/1.00    inference(flattening,[],[f31])).
% 2.58/1.00  
% 2.58/1.00  fof(f56,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f32])).
% 2.58/1.00  
% 2.58/1.00  fof(f64,plain,(
% 2.58/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f13,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f33,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/1.00    inference(ennf_transformation,[],[f13])).
% 2.58/1.00  
% 2.58/1.00  fof(f34,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/1.00    inference(flattening,[],[f33])).
% 2.58/1.00  
% 2.58/1.00  fof(f59,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f7,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f23,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f7])).
% 2.58/1.00  
% 2.58/1.00  fof(f49,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f23])).
% 2.58/1.00  
% 2.58/1.00  fof(f8,axiom,(
% 2.58/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f24,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/1.00    inference(ennf_transformation,[],[f8])).
% 2.58/1.00  
% 2.58/1.00  fof(f25,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/1.00    inference(flattening,[],[f24])).
% 2.58/1.00  
% 2.58/1.00  fof(f51,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f25])).
% 2.58/1.00  
% 2.58/1.00  fof(f11,axiom,(
% 2.58/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f29,plain,(
% 2.58/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f11])).
% 2.58/1.00  
% 2.58/1.00  fof(f30,plain,(
% 2.58/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f29])).
% 2.58/1.00  
% 2.58/1.00  fof(f55,plain,(
% 2.58/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f30])).
% 2.58/1.00  
% 2.58/1.00  fof(f61,plain,(
% 2.58/1.00    ~v2_struct_0(sK1)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f9,axiom,(
% 2.58/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f26,plain,(
% 2.58/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.58/1.00    inference(ennf_transformation,[],[f9])).
% 2.58/1.00  
% 2.58/1.00  fof(f27,plain,(
% 2.58/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.58/1.00    inference(flattening,[],[f26])).
% 2.58/1.00  
% 2.58/1.00  fof(f37,plain,(
% 2.58/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.58/1.00    inference(nnf_transformation,[],[f27])).
% 2.58/1.00  
% 2.58/1.00  fof(f52,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f37])).
% 2.58/1.00  
% 2.58/1.00  fof(f5,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f16,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.58/1.00    inference(pure_predicate_removal,[],[f5])).
% 2.58/1.00  
% 2.58/1.00  fof(f21,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f16])).
% 2.58/1.00  
% 2.58/1.00  fof(f47,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f21])).
% 2.58/1.00  
% 2.58/1.00  fof(f3,axiom,(
% 2.58/1.00    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f18,plain,(
% 2.58/1.00    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f3])).
% 2.58/1.00  
% 2.58/1.00  fof(f45,plain,(
% 2.58/1.00    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f6,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f22,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f6])).
% 2.58/1.00  
% 2.58/1.00  fof(f48,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f22])).
% 2.58/1.00  
% 2.58/1.00  fof(f44,plain,(
% 2.58/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f68,plain,(
% 2.58/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  cnf(c_21,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.58/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_568,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_917,plain,
% 2.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_12,plain,
% 2.58/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_26,negated_conjecture,
% 2.58/1.00      ( l1_struct_0(sK0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_300,plain,
% 2.58/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_301,plain,
% 2.58/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_300]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_564,plain,
% 2.58/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_301]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_24,negated_conjecture,
% 2.58/1.00      ( l1_struct_0(sK1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_295,plain,
% 2.58/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_296,plain,
% 2.58/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_565,plain,
% 2.58/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_296]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_937,plain,
% 2.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.58/1.00      inference(light_normalisation,[status(thm)],[c_917,c_564,c_565]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_0,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/1.00      | ~ v1_relat_1(X1)
% 2.58/1.00      | v1_relat_1(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_579,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.58/1.00      | ~ v1_relat_1(X1_52)
% 2.58/1.00      | v1_relat_1(X0_52) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_908,plain,
% 2.58/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 2.58/1.01      | v1_relat_1(X1_52) != iProver_top
% 2.58/1.01      | v1_relat_1(X0_52) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1171,plain,
% 2.58/1.01      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.58/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_937,c_908]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_32,plain,
% 2.58/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1068,plain,
% 2.58/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.58/1.01      | v1_relat_1(X0_52)
% 2.58/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_579]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1175,plain,
% 2.58/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.58/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.58/1.01      | v1_relat_1(sK2) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_1068]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1176,plain,
% 2.58/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.58/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.58/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1,plain,
% 2.58/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.58/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_578,plain,
% 2.58/1.01      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1187,plain,
% 2.58/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_578]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1188,plain,
% 2.58/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_1187]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1366,plain,
% 2.58/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_1171,c_32,c_1176,c_1188]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_4,plain,
% 2.58/1.01      ( ~ v1_funct_1(X0)
% 2.58/1.01      | ~ v2_funct_1(X0)
% 2.58/1.01      | ~ v1_relat_1(X0)
% 2.58/1.01      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_19,negated_conjecture,
% 2.58/1.01      ( v2_funct_1(sK2) ),
% 2.58/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_393,plain,
% 2.58/1.01      ( ~ v1_funct_1(X0)
% 2.58/1.01      | ~ v1_relat_1(X0)
% 2.58/1.01      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.58/1.01      | sK2 != X0 ),
% 2.58/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_394,plain,
% 2.58/1.01      ( ~ v1_funct_1(sK2)
% 2.58/1.01      | ~ v1_relat_1(sK2)
% 2.58/1.01      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.58/1.01      inference(unflattening,[status(thm)],[c_393]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_23,negated_conjecture,
% 2.58/1.01      ( v1_funct_1(sK2) ),
% 2.58/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_396,plain,
% 2.58/1.01      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_394,c_23]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_562,plain,
% 2.58/1.01      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_396]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_921,plain,
% 2.58/1.01      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.58/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1371,plain,
% 2.58/1.01      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_1366,c_921]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_20,negated_conjecture,
% 2.58/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.58/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_569,negated_conjecture,
% 2.58/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_934,plain,
% 2.58/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_569,c_564,c_565]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_14,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | ~ v2_funct_1(X0)
% 2.58/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.58/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.58/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_369,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.58/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.58/1.01      | sK2 != X0 ),
% 2.58/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_370,plain,
% 2.58/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.58/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.01      | ~ v1_funct_1(sK2)
% 2.58/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.58/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.58/1.01      inference(unflattening,[status(thm)],[c_369]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_374,plain,
% 2.58/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 2.58/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.58/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_370,c_23]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_375,plain,
% 2.58/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.58/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.58/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.58/1.01      inference(renaming,[status(thm)],[c_374]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_563,plain,
% 2.58/1.01      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 2.58/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.58/1.01      | k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.58/1.01      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_375]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_920,plain,
% 2.58/1.01      ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.58/1.01      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
% 2.58/1.01      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 2.58/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1285,plain,
% 2.58/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.58/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.58/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_934,c_920]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_22,negated_conjecture,
% 2.58/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.58/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_567,negated_conjecture,
% 2.58/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_918,plain,
% 2.58/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_931,plain,
% 2.58/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_918,c_564,c_565]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1319,plain,
% 2.58/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_1285,c_937,c_931]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1420,plain,
% 2.58/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1371,c_1319]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_15,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.58/1.01      | ~ v1_funct_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_573,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.58/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.58/1.01      | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.58/1.01      | ~ v1_funct_1(X0_52) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_914,plain,
% 2.58/1.01      ( v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.58/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.58/1.01      | m1_subset_1(k2_tops_2(X0_53,X1_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.58/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1596,plain,
% 2.58/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.58/1.01      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.58/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.58/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_1420,c_914]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_30,plain,
% 2.58/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2714,plain,
% 2.58/1.01      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_1596,c_30,c_937,c_931]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_7,plain,
% 2.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_574,plain,
% 2.58/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.58/1.01      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_913,plain,
% 2.58/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.58/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1491,plain,
% 2.58/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_937,c_913]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1738,plain,
% 2.58/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1491,c_934]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1744,plain,
% 2.58/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1738,c_937]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_8,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | v1_xboole_0(X2)
% 2.58/1.01      | ~ v1_funct_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_13,plain,
% 2.58/1.01      ( v2_struct_0(X0)
% 2.58/1.01      | ~ l1_struct_0(X0)
% 2.58/1.01      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.58/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_25,negated_conjecture,
% 2.58/1.01      ( ~ v2_struct_0(sK1) ),
% 2.58/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_282,plain,
% 2.58/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.58/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_283,plain,
% 2.58/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.58/1.01      inference(unflattening,[status(thm)],[c_282]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_47,plain,
% 2.58/1.01      ( v2_struct_0(sK1)
% 2.58/1.01      | ~ l1_struct_0(sK1)
% 2.58/1.01      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_285,plain,
% 2.58/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_283,c_25,c_24,c_47]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_307,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | k2_struct_0(sK1) != X2 ),
% 2.58/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_285]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_308,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.58/1.01      | v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.58/1.01      | ~ v1_funct_1(X0) ),
% 2.58/1.01      inference(unflattening,[status(thm)],[c_307]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_11,plain,
% 2.58/1.01      ( ~ v1_partfun1(X0,X1)
% 2.58/1.01      | ~ v4_relat_1(X0,X1)
% 2.58/1.01      | ~ v1_relat_1(X0)
% 2.58/1.01      | k1_relat_1(X0) = X1 ),
% 2.58/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_415,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.58/1.01      | ~ v4_relat_1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | ~ v1_relat_1(X0)
% 2.58/1.01      | k1_relat_1(X0) = X1 ),
% 2.58/1.01      inference(resolution,[status(thm)],[c_308,c_11]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_5,plain,
% 2.58/1.01      ( v4_relat_1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.58/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_431,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | ~ v1_relat_1(X0)
% 2.58/1.01      | k1_relat_1(X0) = X1 ),
% 2.58/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_415,c_5]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_561,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0_52,X0_53,k2_struct_0(sK1))
% 2.58/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1))))
% 2.58/1.01      | ~ v1_funct_1(X0_52)
% 2.58/1.01      | ~ v1_relat_1(X0_52)
% 2.58/1.01      | k1_relat_1(X0_52) = X0_53 ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_431]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_922,plain,
% 2.58/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.58/1.01      | v1_funct_2(X0_52,X0_53,k2_struct_0(sK1)) != iProver_top
% 2.58/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1)))) != iProver_top
% 2.58/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.58/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2165,plain,
% 2.58/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.58/1.01      | v1_funct_2(X0_52,X0_53,k2_relat_1(sK2)) != iProver_top
% 2.58/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_relat_1(sK2)))) != iProver_top
% 2.58/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.58/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_922,c_1738]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2175,plain,
% 2.58/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.58/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.58/1.01      | v1_funct_1(sK2) != iProver_top
% 2.58/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_1744,c_2165]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1745,plain,
% 2.58/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1738,c_931]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2591,plain,
% 2.58/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_2175,c_30,c_32,c_1176,c_1188,c_1745]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2718,plain,
% 2.58/1.01      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_2714,c_1738,c_2591]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2722,plain,
% 2.58/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_2718,c_913]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2,plain,
% 2.58/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_577,plain,
% 2.58/1.01      ( ~ v1_relat_1(X0_52)
% 2.58/1.01      | k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_910,plain,
% 2.58/1.01      ( k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52)
% 2.58/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1373,plain,
% 2.58/1.01      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_1366,c_910]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2733,plain,
% 2.58/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_2722,c_1373]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_6,plain,
% 2.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_575,plain,
% 2.58/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.58/1.01      | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_912,plain,
% 2.58/1.01      ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
% 2.58/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2723,plain,
% 2.58/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_2718,c_912]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_3,plain,
% 2.58/1.01      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_576,plain,
% 2.58/1.01      ( ~ v1_relat_1(X0_52)
% 2.58/1.01      | k1_relat_1(k4_relat_1(X0_52)) = k2_relat_1(X0_52) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_911,plain,
% 2.58/1.01      ( k1_relat_1(k4_relat_1(X0_52)) = k2_relat_1(X0_52)
% 2.58/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.58/1.01      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1372,plain,
% 2.58/1.01      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.58/1.01      inference(superposition,[status(thm)],[c_1366,c_911]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2730,plain,
% 2.58/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_2723,c_1372]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_18,negated_conjecture,
% 2.58/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.58/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_570,negated_conjecture,
% 2.58/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.58/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_974,plain,
% 2.58/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.58/1.01      inference(light_normalisation,[status(thm)],[c_570,c_564,c_565]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1322,plain,
% 2.58/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1319,c_974]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1419,plain,
% 2.58/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1371,c_1322]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1741,plain,
% 2.58/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
% 2.58/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_1738,c_1419]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_2594,plain,
% 2.58/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
% 2.58/1.01      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.58/1.01      inference(demodulation,[status(thm)],[c_2591,c_1741]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(contradiction,plain,
% 2.58/1.01      ( $false ),
% 2.58/1.01      inference(minisat,[status(thm)],[c_2733,c_2730,c_2594]) ).
% 2.58/1.01  
% 2.58/1.01  
% 2.58/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.01  
% 2.58/1.01  ------                               Statistics
% 2.58/1.01  
% 2.58/1.01  ------ General
% 2.58/1.01  
% 2.58/1.01  abstr_ref_over_cycles:                  0
% 2.58/1.01  abstr_ref_under_cycles:                 0
% 2.58/1.01  gc_basic_clause_elim:                   0
% 2.58/1.01  forced_gc_time:                         0
% 2.58/1.01  parsing_time:                           0.011
% 2.58/1.01  unif_index_cands_time:                  0.
% 2.58/1.01  unif_index_add_time:                    0.
% 2.58/1.01  orderings_time:                         0.
% 2.58/1.01  out_proof_time:                         0.01
% 2.58/1.01  total_time:                             0.151
% 2.58/1.01  num_of_symbols:                         56
% 2.58/1.01  num_of_terms:                           2446
% 2.58/1.01  
% 2.58/1.01  ------ Preprocessing
% 2.58/1.01  
% 2.58/1.01  num_of_splits:                          0
% 2.58/1.01  num_of_split_atoms:                     0
% 2.58/1.01  num_of_reused_defs:                     0
% 2.58/1.01  num_eq_ax_congr_red:                    6
% 2.58/1.01  num_of_sem_filtered_clauses:            1
% 2.58/1.01  num_of_subtypes:                        4
% 2.58/1.01  monotx_restored_types:                  1
% 2.58/1.01  sat_num_of_epr_types:                   0
% 2.58/1.01  sat_num_of_non_cyclic_types:            0
% 2.58/1.01  sat_guarded_non_collapsed_types:        0
% 2.58/1.01  num_pure_diseq_elim:                    0
% 2.58/1.01  simp_replaced_by:                       0
% 2.58/1.01  res_preprocessed:                       120
% 2.58/1.01  prep_upred:                             0
% 2.58/1.01  prep_unflattend:                        10
% 2.58/1.01  smt_new_axioms:                         0
% 2.58/1.01  pred_elim_cands:                        4
% 2.58/1.01  pred_elim:                              6
% 2.58/1.01  pred_elim_cl:                           7
% 2.58/1.01  pred_elim_cycles:                       9
% 2.58/1.01  merged_defs:                            0
% 2.58/1.01  merged_defs_ncl:                        0
% 2.58/1.01  bin_hyper_res:                          0
% 2.58/1.01  prep_cycles:                            4
% 2.58/1.01  pred_elim_time:                         0.004
% 2.58/1.01  splitting_time:                         0.
% 2.58/1.01  sem_filter_time:                        0.
% 2.58/1.01  monotx_time:                            0.
% 2.58/1.01  subtype_inf_time:                       0.002
% 2.58/1.01  
% 2.58/1.01  ------ Problem properties
% 2.58/1.01  
% 2.58/1.01  clauses:                                19
% 2.58/1.01  conjectures:                            5
% 2.58/1.01  epr:                                    1
% 2.58/1.01  horn:                                   19
% 2.58/1.01  ground:                                 8
% 2.58/1.01  unary:                                  7
% 2.58/1.01  binary:                                 6
% 2.58/1.01  lits:                                   43
% 2.58/1.01  lits_eq:                                13
% 2.58/1.01  fd_pure:                                0
% 2.58/1.01  fd_pseudo:                              0
% 2.58/1.01  fd_cond:                                0
% 2.58/1.01  fd_pseudo_cond:                         1
% 2.58/1.01  ac_symbols:                             0
% 2.58/1.01  
% 2.58/1.01  ------ Propositional Solver
% 2.58/1.01  
% 2.58/1.01  prop_solver_calls:                      30
% 2.58/1.01  prop_fast_solver_calls:                 726
% 2.58/1.01  smt_solver_calls:                       0
% 2.58/1.01  smt_fast_solver_calls:                  0
% 2.58/1.01  prop_num_of_clauses:                    941
% 2.58/1.01  prop_preprocess_simplified:             3589
% 2.58/1.01  prop_fo_subsumed:                       19
% 2.58/1.01  prop_solver_time:                       0.
% 2.58/1.01  smt_solver_time:                        0.
% 2.58/1.01  smt_fast_solver_time:                   0.
% 2.58/1.01  prop_fast_solver_time:                  0.
% 2.58/1.01  prop_unsat_core_time:                   0.
% 2.58/1.01  
% 2.58/1.01  ------ QBF
% 2.58/1.01  
% 2.58/1.01  qbf_q_res:                              0
% 2.58/1.01  qbf_num_tautologies:                    0
% 2.58/1.01  qbf_prep_cycles:                        0
% 2.58/1.01  
% 2.58/1.01  ------ BMC1
% 2.58/1.01  
% 2.58/1.01  bmc1_current_bound:                     -1
% 2.58/1.01  bmc1_last_solved_bound:                 -1
% 2.58/1.01  bmc1_unsat_core_size:                   -1
% 2.58/1.01  bmc1_unsat_core_parents_size:           -1
% 2.58/1.01  bmc1_merge_next_fun:                    0
% 2.58/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.01  
% 2.58/1.01  ------ Instantiation
% 2.58/1.01  
% 2.58/1.01  inst_num_of_clauses:                    315
% 2.58/1.01  inst_num_in_passive:                    90
% 2.58/1.01  inst_num_in_active:                     223
% 2.58/1.01  inst_num_in_unprocessed:                2
% 2.58/1.01  inst_num_of_loops:                      240
% 2.58/1.01  inst_num_of_learning_restarts:          0
% 2.58/1.01  inst_num_moves_active_passive:          11
% 2.58/1.01  inst_lit_activity:                      0
% 2.58/1.01  inst_lit_activity_moves:                0
% 2.58/1.01  inst_num_tautologies:                   0
% 2.58/1.01  inst_num_prop_implied:                  0
% 2.58/1.01  inst_num_existing_simplified:           0
% 2.58/1.01  inst_num_eq_res_simplified:             0
% 2.58/1.01  inst_num_child_elim:                    0
% 2.58/1.01  inst_num_of_dismatching_blockings:      127
% 2.58/1.01  inst_num_of_non_proper_insts:           357
% 2.58/1.01  inst_num_of_duplicates:                 0
% 2.58/1.01  inst_inst_num_from_inst_to_res:         0
% 2.58/1.01  inst_dismatching_checking_time:         0.
% 2.58/1.01  
% 2.58/1.01  ------ Resolution
% 2.58/1.01  
% 2.58/1.01  res_num_of_clauses:                     0
% 2.58/1.01  res_num_in_passive:                     0
% 2.58/1.01  res_num_in_active:                      0
% 2.58/1.01  res_num_of_loops:                       124
% 2.58/1.01  res_forward_subset_subsumed:            49
% 2.58/1.01  res_backward_subset_subsumed:           0
% 2.58/1.01  res_forward_subsumed:                   0
% 2.58/1.01  res_backward_subsumed:                  0
% 2.58/1.01  res_forward_subsumption_resolution:     1
% 2.58/1.01  res_backward_subsumption_resolution:    0
% 2.58/1.01  res_clause_to_clause_subsumption:       72
% 2.58/1.01  res_orphan_elimination:                 0
% 2.58/1.01  res_tautology_del:                      54
% 2.58/1.01  res_num_eq_res_simplified:              0
% 2.58/1.01  res_num_sel_changes:                    0
% 2.58/1.01  res_moves_from_active_to_pass:          0
% 2.58/1.01  
% 2.58/1.01  ------ Superposition
% 2.58/1.01  
% 2.58/1.01  sup_time_total:                         0.
% 2.58/1.01  sup_time_generating:                    0.
% 2.58/1.01  sup_time_sim_full:                      0.
% 2.58/1.01  sup_time_sim_immed:                     0.
% 2.58/1.01  
% 2.58/1.01  sup_num_of_clauses:                     41
% 2.58/1.01  sup_num_in_active:                      26
% 2.58/1.01  sup_num_in_passive:                     15
% 2.58/1.01  sup_num_of_loops:                       46
% 2.58/1.01  sup_fw_superposition:                   12
% 2.58/1.01  sup_bw_superposition:                   17
% 2.58/1.01  sup_immediate_simplified:               6
% 2.58/1.01  sup_given_eliminated:                   0
% 2.58/1.01  comparisons_done:                       0
% 2.58/1.01  comparisons_avoided:                    0
% 2.58/1.01  
% 2.58/1.01  ------ Simplifications
% 2.58/1.01  
% 2.58/1.01  
% 2.58/1.01  sim_fw_subset_subsumed:                 2
% 2.58/1.01  sim_bw_subset_subsumed:                 2
% 2.58/1.01  sim_fw_subsumed:                        0
% 2.58/1.01  sim_bw_subsumed:                        0
% 2.58/1.01  sim_fw_subsumption_res:                 0
% 2.58/1.01  sim_bw_subsumption_res:                 0
% 2.58/1.01  sim_tautology_del:                      0
% 2.58/1.01  sim_eq_tautology_del:                   0
% 2.58/1.01  sim_eq_res_simp:                        0
% 2.58/1.01  sim_fw_demodulated:                     0
% 2.58/1.01  sim_bw_demodulated:                     20
% 2.58/1.01  sim_light_normalised:                   11
% 2.58/1.01  sim_joinable_taut:                      0
% 2.58/1.01  sim_joinable_simp:                      0
% 2.58/1.01  sim_ac_normalised:                      0
% 2.58/1.01  sim_smt_subsumption:                    0
% 2.58/1.01  
%------------------------------------------------------------------------------
