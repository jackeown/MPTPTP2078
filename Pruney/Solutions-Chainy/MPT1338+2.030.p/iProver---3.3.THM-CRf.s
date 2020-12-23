%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:05 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  203 (2881 expanded)
%              Number of clauses        :  133 ( 912 expanded)
%              Number of leaves         :   21 ( 803 expanded)
%              Depth                    :   21
%              Number of atoms          :  617 (19513 expanded)
%              Number of equality atoms :  278 (6560 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1117,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1524,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_358,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_359,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1112,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_353,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_354,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1113,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1524,c_1112,c_1113])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1123,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1520,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_1832,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1551,c_1520])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1118,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1548,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1118,c_1112,c_1113])).

cnf(c_2387,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1832,c_1548])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_600,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_601,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_26])).

cnf(c_606,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_1106,plain,
    ( ~ v1_funct_2(sK2,X0_57,X1_57)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,sK2) != X1_57 ),
    inference(subtyping,[status(esa)],[c_606])).

cnf(c_1532,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_624,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_625,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_26])).

cnf(c_1105,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_1533,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1702,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1834,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1533,c_24,c_1105,c_1702])).

cnf(c_2040,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1532,c_1834])).

cnf(c_2048,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_2040])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1116,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1525,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_1545,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1525,c_1112,c_1113])).

cnf(c_2313,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2048,c_1551,c_1545])).

cnf(c_2508,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2387,c_2313])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1121,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k8_relset_1(X0_57,X1_57,X0_56,X1_57) = k1_relset_1(X0_57,X1_57,X0_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1522,plain,
    ( k8_relset_1(X0_57,X1_57,X0_56,X1_57) = k1_relset_1(X0_57,X1_57,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_3083,plain,
    ( k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),k2_struct_0(sK0)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2508,c_1522])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k8_relset_1(X0_57,X1_57,X0_56,X2_57) = k10_relat_1(X0_56,X2_57) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1521,plain,
    ( k8_relset_1(X0_57,X1_57,X0_56,X2_57) = k10_relat_1(X0_56,X2_57)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_3084,plain,
    ( k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),X0_57) = k10_relat_1(k4_relat_1(sK2),X0_57) ),
    inference(superposition,[status(thm)],[c_2508,c_1521])).

cnf(c_3091,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k10_relat_1(k4_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_3083,c_3084])).

cnf(c_1519,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_2322,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_1519])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1127,plain,
    ( ~ v1_relat_1(X0_56)
    | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1516,plain,
    ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_2375,plain,
    ( k10_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2322,c_1516])).

cnf(c_1747,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1519])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1125,plain,
    ( ~ v1_relat_1(X0_56)
    | k1_relat_1(k4_relat_1(X0_56)) = k2_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1518,plain,
    ( k1_relat_1(k4_relat_1(X0_56)) = k2_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_2262,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1747,c_1518])).

cnf(c_2384,plain,
    ( k10_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2375,c_2262])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1126,plain,
    ( ~ v1_relat_1(X0_56)
    | k2_relat_1(k4_relat_1(X0_56)) = k1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1517,plain,
    ( k2_relat_1(k4_relat_1(X0_56)) = k1_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_2263,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1747,c_1517])).

cnf(c_3310,plain,
    ( k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2384,c_2263])).

cnf(c_2513,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2387,c_1551])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_365,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_12])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_12,c_6,c_5])).

cnf(c_370,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_469,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_14,c_370])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_14,c_5,c_365])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1111,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_56)
    | k1_relat_1(X0_56) = X0_57
    | k1_xboole_0 = X1_57 ),
    inference(subtyping,[status(esa)],[c_474])).

cnf(c_1527,plain,
    ( k1_relat_1(X0_56) = X0_57
    | k1_xboole_0 = X1_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_2999,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2513,c_1527])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_326,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_344,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_28])).

cnf(c_345,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_328,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_347,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_28,c_27,c_328])).

cnf(c_1114,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(c_1134,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_1707,plain,
    ( u1_struct_0(sK1) != X0_57
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != X0_57 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1782,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_1130,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_1783,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1779,plain,
    ( X0_57 != X1_57
    | X0_57 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1_57 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1853,plain,
    ( X0_57 = u1_struct_0(sK0)
    | X0_57 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_1906,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = u1_struct_0(sK0)
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_1907,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1843,plain,
    ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_56)
    | k1_relat_1(X0_56) = X0_57
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1993,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_2056,plain,
    ( X0_57 != X1_57
    | k2_struct_0(sK0) != X1_57
    | k2_struct_0(sK0) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_2699,plain,
    ( X0_57 != u1_struct_0(sK0)
    | k2_struct_0(sK0) = X0_57
    | k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2995,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3514,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2999,c_26,c_25,c_24,c_1114,c_1112,c_1782,c_1783,c_1906,c_1907,c_1993,c_2995])).

cnf(c_3671,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3091,c_3310,c_3514])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_529,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_533,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_26])).

cnf(c_534,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_533])).

cnf(c_1109,plain,
    ( ~ v1_funct_2(sK2,X0_57,X1_57)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_534])).

cnf(c_1529,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1919,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | k2_tops_2(X0_57,X1_57,sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1529,c_1834])).

cnf(c_1927,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1919])).

cnf(c_1954,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_1551,c_1545])).

cnf(c_21,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1119,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1590,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1119,c_1112,c_1113])).

cnf(c_1957,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1954,c_1590])).

cnf(c_2511,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2387,c_1957])).

cnf(c_2321,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2313,c_1520])).

cnf(c_3019,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2321,c_2263,c_2387])).

cnf(c_3409,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2511,c_3019])).

cnf(c_3412,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3409,c_26,c_25,c_24,c_1114,c_1112,c_1782,c_1783,c_1906,c_1907,c_1993,c_2995])).

cnf(c_3519,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3514,c_3412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3671,c_3519])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.68/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/0.99  
% 2.68/0.99  ------  iProver source info
% 2.68/0.99  
% 2.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/0.99  git: non_committed_changes: false
% 2.68/0.99  git: last_make_outside_of_git: false
% 2.68/0.99  
% 2.68/0.99  ------ 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options
% 2.68/0.99  
% 2.68/0.99  --out_options                           all
% 2.68/0.99  --tptp_safe_out                         true
% 2.68/0.99  --problem_path                          ""
% 2.68/0.99  --include_path                          ""
% 2.68/0.99  --clausifier                            res/vclausify_rel
% 2.68/0.99  --clausifier_options                    --mode clausify
% 2.68/0.99  --stdin                                 false
% 2.68/0.99  --stats_out                             all
% 2.68/0.99  
% 2.68/0.99  ------ General Options
% 2.68/0.99  
% 2.68/0.99  --fof                                   false
% 2.68/0.99  --time_out_real                         305.
% 2.68/0.99  --time_out_virtual                      -1.
% 2.68/0.99  --symbol_type_check                     false
% 2.68/0.99  --clausify_out                          false
% 2.68/0.99  --sig_cnt_out                           false
% 2.68/0.99  --trig_cnt_out                          false
% 2.68/0.99  --trig_cnt_out_tolerance                1.
% 2.68/0.99  --trig_cnt_out_sk_spl                   false
% 2.68/0.99  --abstr_cl_out                          false
% 2.68/0.99  
% 2.68/0.99  ------ Global Options
% 2.68/0.99  
% 2.68/0.99  --schedule                              default
% 2.68/0.99  --add_important_lit                     false
% 2.68/0.99  --prop_solver_per_cl                    1000
% 2.68/0.99  --min_unsat_core                        false
% 2.68/0.99  --soft_assumptions                      false
% 2.68/0.99  --soft_lemma_size                       3
% 2.68/0.99  --prop_impl_unit_size                   0
% 2.68/0.99  --prop_impl_unit                        []
% 2.68/0.99  --share_sel_clauses                     true
% 2.68/0.99  --reset_solvers                         false
% 2.68/0.99  --bc_imp_inh                            [conj_cone]
% 2.68/0.99  --conj_cone_tolerance                   3.
% 2.68/0.99  --extra_neg_conj                        none
% 2.68/0.99  --large_theory_mode                     true
% 2.68/0.99  --prolific_symb_bound                   200
% 2.68/0.99  --lt_threshold                          2000
% 2.68/0.99  --clause_weak_htbl                      true
% 2.68/0.99  --gc_record_bc_elim                     false
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing Options
% 2.68/0.99  
% 2.68/0.99  --preprocessing_flag                    true
% 2.68/0.99  --time_out_prep_mult                    0.1
% 2.68/0.99  --splitting_mode                        input
% 2.68/0.99  --splitting_grd                         true
% 2.68/0.99  --splitting_cvd                         false
% 2.68/0.99  --splitting_cvd_svl                     false
% 2.68/0.99  --splitting_nvd                         32
% 2.68/0.99  --sub_typing                            true
% 2.68/0.99  --prep_gs_sim                           true
% 2.68/0.99  --prep_unflatten                        true
% 2.68/0.99  --prep_res_sim                          true
% 2.68/0.99  --prep_upred                            true
% 2.68/0.99  --prep_sem_filter                       exhaustive
% 2.68/0.99  --prep_sem_filter_out                   false
% 2.68/0.99  --pred_elim                             true
% 2.68/0.99  --res_sim_input                         true
% 2.68/0.99  --eq_ax_congr_red                       true
% 2.68/0.99  --pure_diseq_elim                       true
% 2.68/0.99  --brand_transform                       false
% 2.68/0.99  --non_eq_to_eq                          false
% 2.68/0.99  --prep_def_merge                        true
% 2.68/0.99  --prep_def_merge_prop_impl              false
% 2.68/0.99  --prep_def_merge_mbd                    true
% 2.68/0.99  --prep_def_merge_tr_red                 false
% 2.68/0.99  --prep_def_merge_tr_cl                  false
% 2.68/0.99  --smt_preprocessing                     true
% 2.68/0.99  --smt_ac_axioms                         fast
% 2.68/0.99  --preprocessed_out                      false
% 2.68/0.99  --preprocessed_stats                    false
% 2.68/0.99  
% 2.68/0.99  ------ Abstraction refinement Options
% 2.68/0.99  
% 2.68/0.99  --abstr_ref                             []
% 2.68/0.99  --abstr_ref_prep                        false
% 2.68/0.99  --abstr_ref_until_sat                   false
% 2.68/0.99  --abstr_ref_sig_restrict                funpre
% 2.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.99  --abstr_ref_under                       []
% 2.68/0.99  
% 2.68/0.99  ------ SAT Options
% 2.68/0.99  
% 2.68/0.99  --sat_mode                              false
% 2.68/0.99  --sat_fm_restart_options                ""
% 2.68/0.99  --sat_gr_def                            false
% 2.68/0.99  --sat_epr_types                         true
% 2.68/0.99  --sat_non_cyclic_types                  false
% 2.68/0.99  --sat_finite_models                     false
% 2.68/0.99  --sat_fm_lemmas                         false
% 2.68/0.99  --sat_fm_prep                           false
% 2.68/0.99  --sat_fm_uc_incr                        true
% 2.68/0.99  --sat_out_model                         small
% 2.68/0.99  --sat_out_clauses                       false
% 2.68/0.99  
% 2.68/0.99  ------ QBF Options
% 2.68/0.99  
% 2.68/0.99  --qbf_mode                              false
% 2.68/0.99  --qbf_elim_univ                         false
% 2.68/0.99  --qbf_dom_inst                          none
% 2.68/0.99  --qbf_dom_pre_inst                      false
% 2.68/0.99  --qbf_sk_in                             false
% 2.68/0.99  --qbf_pred_elim                         true
% 2.68/0.99  --qbf_split                             512
% 2.68/0.99  
% 2.68/0.99  ------ BMC1 Options
% 2.68/0.99  
% 2.68/0.99  --bmc1_incremental                      false
% 2.68/0.99  --bmc1_axioms                           reachable_all
% 2.68/0.99  --bmc1_min_bound                        0
% 2.68/0.99  --bmc1_max_bound                        -1
% 2.68/0.99  --bmc1_max_bound_default                -1
% 2.68/0.99  --bmc1_symbol_reachability              true
% 2.68/0.99  --bmc1_property_lemmas                  false
% 2.68/0.99  --bmc1_k_induction                      false
% 2.68/0.99  --bmc1_non_equiv_states                 false
% 2.68/0.99  --bmc1_deadlock                         false
% 2.68/0.99  --bmc1_ucm                              false
% 2.68/0.99  --bmc1_add_unsat_core                   none
% 2.68/0.99  --bmc1_unsat_core_children              false
% 2.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.99  --bmc1_out_stat                         full
% 2.68/0.99  --bmc1_ground_init                      false
% 2.68/0.99  --bmc1_pre_inst_next_state              false
% 2.68/0.99  --bmc1_pre_inst_state                   false
% 2.68/0.99  --bmc1_pre_inst_reach_state             false
% 2.68/0.99  --bmc1_out_unsat_core                   false
% 2.68/0.99  --bmc1_aig_witness_out                  false
% 2.68/0.99  --bmc1_verbose                          false
% 2.68/0.99  --bmc1_dump_clauses_tptp                false
% 2.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.99  --bmc1_dump_file                        -
% 2.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.99  --bmc1_ucm_extend_mode                  1
% 2.68/0.99  --bmc1_ucm_init_mode                    2
% 2.68/0.99  --bmc1_ucm_cone_mode                    none
% 2.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.99  --bmc1_ucm_relax_model                  4
% 2.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.99  --bmc1_ucm_layered_model                none
% 2.68/0.99  --bmc1_ucm_max_lemma_size               10
% 2.68/0.99  
% 2.68/0.99  ------ AIG Options
% 2.68/0.99  
% 2.68/0.99  --aig_mode                              false
% 2.68/0.99  
% 2.68/0.99  ------ Instantiation Options
% 2.68/0.99  
% 2.68/0.99  --instantiation_flag                    true
% 2.68/0.99  --inst_sos_flag                         false
% 2.68/0.99  --inst_sos_phase                        true
% 2.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel_side                     num_symb
% 2.68/0.99  --inst_solver_per_active                1400
% 2.68/0.99  --inst_solver_calls_frac                1.
% 2.68/0.99  --inst_passive_queue_type               priority_queues
% 2.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.99  --inst_passive_queues_freq              [25;2]
% 2.68/0.99  --inst_dismatching                      true
% 2.68/0.99  --inst_eager_unprocessed_to_passive     true
% 2.68/0.99  --inst_prop_sim_given                   true
% 2.68/0.99  --inst_prop_sim_new                     false
% 2.68/0.99  --inst_subs_new                         false
% 2.68/0.99  --inst_eq_res_simp                      false
% 2.68/0.99  --inst_subs_given                       false
% 2.68/0.99  --inst_orphan_elimination               true
% 2.68/0.99  --inst_learning_loop_flag               true
% 2.68/0.99  --inst_learning_start                   3000
% 2.68/0.99  --inst_learning_factor                  2
% 2.68/0.99  --inst_start_prop_sim_after_learn       3
% 2.68/0.99  --inst_sel_renew                        solver
% 2.68/0.99  --inst_lit_activity_flag                true
% 2.68/0.99  --inst_restr_to_given                   false
% 2.68/0.99  --inst_activity_threshold               500
% 2.68/0.99  --inst_out_proof                        true
% 2.68/0.99  
% 2.68/0.99  ------ Resolution Options
% 2.68/0.99  
% 2.68/0.99  --resolution_flag                       true
% 2.68/0.99  --res_lit_sel                           adaptive
% 2.68/0.99  --res_lit_sel_side                      none
% 2.68/0.99  --res_ordering                          kbo
% 2.68/0.99  --res_to_prop_solver                    active
% 2.68/0.99  --res_prop_simpl_new                    false
% 2.68/0.99  --res_prop_simpl_given                  true
% 2.68/0.99  --res_passive_queue_type                priority_queues
% 2.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.99  --res_passive_queues_freq               [15;5]
% 2.68/0.99  --res_forward_subs                      full
% 2.68/0.99  --res_backward_subs                     full
% 2.68/0.99  --res_forward_subs_resolution           true
% 2.68/0.99  --res_backward_subs_resolution          true
% 2.68/0.99  --res_orphan_elimination                true
% 2.68/0.99  --res_time_limit                        2.
% 2.68/0.99  --res_out_proof                         true
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Options
% 2.68/0.99  
% 2.68/0.99  --superposition_flag                    true
% 2.68/0.99  --sup_passive_queue_type                priority_queues
% 2.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.99  --demod_completeness_check              fast
% 2.68/0.99  --demod_use_ground                      true
% 2.68/0.99  --sup_to_prop_solver                    passive
% 2.68/0.99  --sup_prop_simpl_new                    true
% 2.68/0.99  --sup_prop_simpl_given                  true
% 2.68/0.99  --sup_fun_splitting                     false
% 2.68/0.99  --sup_smt_interval                      50000
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Simplification Setup
% 2.68/0.99  
% 2.68/0.99  --sup_indices_passive                   []
% 2.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_full_bw                           [BwDemod]
% 2.68/0.99  --sup_immed_triv                        [TrivRules]
% 2.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_immed_bw_main                     []
% 2.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  
% 2.68/0.99  ------ Combination Options
% 2.68/0.99  
% 2.68/0.99  --comb_res_mult                         3
% 2.68/0.99  --comb_sup_mult                         2
% 2.68/0.99  --comb_inst_mult                        10
% 2.68/0.99  
% 2.68/0.99  ------ Debug Options
% 2.68/0.99  
% 2.68/0.99  --dbg_backtrace                         false
% 2.68/0.99  --dbg_dump_prop_clauses                 false
% 2.68/0.99  --dbg_dump_prop_clauses_file            -
% 2.68/0.99  --dbg_out_stat                          false
% 2.68/0.99  ------ Parsing...
% 2.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/0.99  ------ Proving...
% 2.68/0.99  ------ Problem Properties 
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  clauses                                 23
% 2.68/0.99  conjectures                             5
% 2.68/0.99  EPR                                     1
% 2.68/0.99  Horn                                    22
% 2.68/0.99  unary                                   7
% 2.68/0.99  binary                                  10
% 2.68/0.99  lits                                    53
% 2.68/0.99  lits eq                                 22
% 2.68/0.99  fd_pure                                 0
% 2.68/0.99  fd_pseudo                               0
% 2.68/0.99  fd_cond                                 0
% 2.68/0.99  fd_pseudo_cond                          1
% 2.68/0.99  AC symbols                              0
% 2.68/0.99  
% 2.68/0.99  ------ Schedule dynamic 5 is on 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  ------ 
% 2.68/0.99  Current options:
% 2.68/0.99  ------ 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options
% 2.68/0.99  
% 2.68/0.99  --out_options                           all
% 2.68/0.99  --tptp_safe_out                         true
% 2.68/0.99  --problem_path                          ""
% 2.68/0.99  --include_path                          ""
% 2.68/0.99  --clausifier                            res/vclausify_rel
% 2.68/0.99  --clausifier_options                    --mode clausify
% 2.68/0.99  --stdin                                 false
% 2.68/0.99  --stats_out                             all
% 2.68/0.99  
% 2.68/0.99  ------ General Options
% 2.68/0.99  
% 2.68/0.99  --fof                                   false
% 2.68/0.99  --time_out_real                         305.
% 2.68/0.99  --time_out_virtual                      -1.
% 2.68/0.99  --symbol_type_check                     false
% 2.68/0.99  --clausify_out                          false
% 2.68/0.99  --sig_cnt_out                           false
% 2.68/0.99  --trig_cnt_out                          false
% 2.68/0.99  --trig_cnt_out_tolerance                1.
% 2.68/0.99  --trig_cnt_out_sk_spl                   false
% 2.68/0.99  --abstr_cl_out                          false
% 2.68/0.99  
% 2.68/0.99  ------ Global Options
% 2.68/0.99  
% 2.68/0.99  --schedule                              default
% 2.68/0.99  --add_important_lit                     false
% 2.68/0.99  --prop_solver_per_cl                    1000
% 2.68/0.99  --min_unsat_core                        false
% 2.68/0.99  --soft_assumptions                      false
% 2.68/0.99  --soft_lemma_size                       3
% 2.68/0.99  --prop_impl_unit_size                   0
% 2.68/0.99  --prop_impl_unit                        []
% 2.68/0.99  --share_sel_clauses                     true
% 2.68/0.99  --reset_solvers                         false
% 2.68/0.99  --bc_imp_inh                            [conj_cone]
% 2.68/0.99  --conj_cone_tolerance                   3.
% 2.68/0.99  --extra_neg_conj                        none
% 2.68/0.99  --large_theory_mode                     true
% 2.68/0.99  --prolific_symb_bound                   200
% 2.68/0.99  --lt_threshold                          2000
% 2.68/0.99  --clause_weak_htbl                      true
% 2.68/0.99  --gc_record_bc_elim                     false
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing Options
% 2.68/0.99  
% 2.68/0.99  --preprocessing_flag                    true
% 2.68/0.99  --time_out_prep_mult                    0.1
% 2.68/0.99  --splitting_mode                        input
% 2.68/0.99  --splitting_grd                         true
% 2.68/0.99  --splitting_cvd                         false
% 2.68/0.99  --splitting_cvd_svl                     false
% 2.68/0.99  --splitting_nvd                         32
% 2.68/0.99  --sub_typing                            true
% 2.68/0.99  --prep_gs_sim                           true
% 2.68/0.99  --prep_unflatten                        true
% 2.68/0.99  --prep_res_sim                          true
% 2.68/0.99  --prep_upred                            true
% 2.68/0.99  --prep_sem_filter                       exhaustive
% 2.68/0.99  --prep_sem_filter_out                   false
% 2.68/0.99  --pred_elim                             true
% 2.68/0.99  --res_sim_input                         true
% 2.68/0.99  --eq_ax_congr_red                       true
% 2.68/0.99  --pure_diseq_elim                       true
% 2.68/0.99  --brand_transform                       false
% 2.68/0.99  --non_eq_to_eq                          false
% 2.68/0.99  --prep_def_merge                        true
% 2.68/0.99  --prep_def_merge_prop_impl              false
% 2.68/0.99  --prep_def_merge_mbd                    true
% 2.68/0.99  --prep_def_merge_tr_red                 false
% 2.68/0.99  --prep_def_merge_tr_cl                  false
% 2.68/0.99  --smt_preprocessing                     true
% 2.68/0.99  --smt_ac_axioms                         fast
% 2.68/0.99  --preprocessed_out                      false
% 2.68/0.99  --preprocessed_stats                    false
% 2.68/0.99  
% 2.68/0.99  ------ Abstraction refinement Options
% 2.68/0.99  
% 2.68/0.99  --abstr_ref                             []
% 2.68/0.99  --abstr_ref_prep                        false
% 2.68/0.99  --abstr_ref_until_sat                   false
% 2.68/0.99  --abstr_ref_sig_restrict                funpre
% 2.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.99  --abstr_ref_under                       []
% 2.68/0.99  
% 2.68/0.99  ------ SAT Options
% 2.68/0.99  
% 2.68/0.99  --sat_mode                              false
% 2.68/0.99  --sat_fm_restart_options                ""
% 2.68/0.99  --sat_gr_def                            false
% 2.68/0.99  --sat_epr_types                         true
% 2.68/0.99  --sat_non_cyclic_types                  false
% 2.68/0.99  --sat_finite_models                     false
% 2.68/0.99  --sat_fm_lemmas                         false
% 2.68/0.99  --sat_fm_prep                           false
% 2.68/0.99  --sat_fm_uc_incr                        true
% 2.68/0.99  --sat_out_model                         small
% 2.68/0.99  --sat_out_clauses                       false
% 2.68/0.99  
% 2.68/0.99  ------ QBF Options
% 2.68/0.99  
% 2.68/0.99  --qbf_mode                              false
% 2.68/0.99  --qbf_elim_univ                         false
% 2.68/0.99  --qbf_dom_inst                          none
% 2.68/0.99  --qbf_dom_pre_inst                      false
% 2.68/0.99  --qbf_sk_in                             false
% 2.68/0.99  --qbf_pred_elim                         true
% 2.68/0.99  --qbf_split                             512
% 2.68/0.99  
% 2.68/0.99  ------ BMC1 Options
% 2.68/0.99  
% 2.68/0.99  --bmc1_incremental                      false
% 2.68/0.99  --bmc1_axioms                           reachable_all
% 2.68/0.99  --bmc1_min_bound                        0
% 2.68/0.99  --bmc1_max_bound                        -1
% 2.68/0.99  --bmc1_max_bound_default                -1
% 2.68/0.99  --bmc1_symbol_reachability              true
% 2.68/0.99  --bmc1_property_lemmas                  false
% 2.68/0.99  --bmc1_k_induction                      false
% 2.68/0.99  --bmc1_non_equiv_states                 false
% 2.68/0.99  --bmc1_deadlock                         false
% 2.68/0.99  --bmc1_ucm                              false
% 2.68/0.99  --bmc1_add_unsat_core                   none
% 2.68/0.99  --bmc1_unsat_core_children              false
% 2.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.99  --bmc1_out_stat                         full
% 2.68/0.99  --bmc1_ground_init                      false
% 2.68/0.99  --bmc1_pre_inst_next_state              false
% 2.68/0.99  --bmc1_pre_inst_state                   false
% 2.68/0.99  --bmc1_pre_inst_reach_state             false
% 2.68/0.99  --bmc1_out_unsat_core                   false
% 2.68/0.99  --bmc1_aig_witness_out                  false
% 2.68/0.99  --bmc1_verbose                          false
% 2.68/0.99  --bmc1_dump_clauses_tptp                false
% 2.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.99  --bmc1_dump_file                        -
% 2.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.99  --bmc1_ucm_extend_mode                  1
% 2.68/0.99  --bmc1_ucm_init_mode                    2
% 2.68/0.99  --bmc1_ucm_cone_mode                    none
% 2.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.99  --bmc1_ucm_relax_model                  4
% 2.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.99  --bmc1_ucm_layered_model                none
% 2.68/0.99  --bmc1_ucm_max_lemma_size               10
% 2.68/0.99  
% 2.68/0.99  ------ AIG Options
% 2.68/0.99  
% 2.68/0.99  --aig_mode                              false
% 2.68/0.99  
% 2.68/0.99  ------ Instantiation Options
% 2.68/0.99  
% 2.68/0.99  --instantiation_flag                    true
% 2.68/0.99  --inst_sos_flag                         false
% 2.68/0.99  --inst_sos_phase                        true
% 2.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel_side                     none
% 2.68/0.99  --inst_solver_per_active                1400
% 2.68/0.99  --inst_solver_calls_frac                1.
% 2.68/0.99  --inst_passive_queue_type               priority_queues
% 2.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.99  --inst_passive_queues_freq              [25;2]
% 2.68/0.99  --inst_dismatching                      true
% 2.68/0.99  --inst_eager_unprocessed_to_passive     true
% 2.68/0.99  --inst_prop_sim_given                   true
% 2.68/0.99  --inst_prop_sim_new                     false
% 2.68/0.99  --inst_subs_new                         false
% 2.68/0.99  --inst_eq_res_simp                      false
% 2.68/0.99  --inst_subs_given                       false
% 2.68/0.99  --inst_orphan_elimination               true
% 2.68/0.99  --inst_learning_loop_flag               true
% 2.68/0.99  --inst_learning_start                   3000
% 2.68/0.99  --inst_learning_factor                  2
% 2.68/0.99  --inst_start_prop_sim_after_learn       3
% 2.68/0.99  --inst_sel_renew                        solver
% 2.68/0.99  --inst_lit_activity_flag                true
% 2.68/0.99  --inst_restr_to_given                   false
% 2.68/0.99  --inst_activity_threshold               500
% 2.68/0.99  --inst_out_proof                        true
% 2.68/0.99  
% 2.68/0.99  ------ Resolution Options
% 2.68/0.99  
% 2.68/0.99  --resolution_flag                       false
% 2.68/0.99  --res_lit_sel                           adaptive
% 2.68/0.99  --res_lit_sel_side                      none
% 2.68/0.99  --res_ordering                          kbo
% 2.68/0.99  --res_to_prop_solver                    active
% 2.68/0.99  --res_prop_simpl_new                    false
% 2.68/0.99  --res_prop_simpl_given                  true
% 2.68/0.99  --res_passive_queue_type                priority_queues
% 2.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.99  --res_passive_queues_freq               [15;5]
% 2.68/0.99  --res_forward_subs                      full
% 2.68/0.99  --res_backward_subs                     full
% 2.68/0.99  --res_forward_subs_resolution           true
% 2.68/0.99  --res_backward_subs_resolution          true
% 2.68/0.99  --res_orphan_elimination                true
% 2.68/0.99  --res_time_limit                        2.
% 2.68/0.99  --res_out_proof                         true
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Options
% 2.68/0.99  
% 2.68/0.99  --superposition_flag                    true
% 2.68/0.99  --sup_passive_queue_type                priority_queues
% 2.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.99  --demod_completeness_check              fast
% 2.68/0.99  --demod_use_ground                      true
% 2.68/0.99  --sup_to_prop_solver                    passive
% 2.68/0.99  --sup_prop_simpl_new                    true
% 2.68/0.99  --sup_prop_simpl_given                  true
% 2.68/0.99  --sup_fun_splitting                     false
% 2.68/0.99  --sup_smt_interval                      50000
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Simplification Setup
% 2.68/0.99  
% 2.68/0.99  --sup_indices_passive                   []
% 2.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_full_bw                           [BwDemod]
% 2.68/0.99  --sup_immed_triv                        [TrivRules]
% 2.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_immed_bw_main                     []
% 2.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  
% 2.68/0.99  ------ Combination Options
% 2.68/0.99  
% 2.68/0.99  --comb_res_mult                         3
% 2.68/0.99  --comb_sup_mult                         2
% 2.68/0.99  --comb_inst_mult                        10
% 2.68/0.99  
% 2.68/0.99  ------ Debug Options
% 2.68/0.99  
% 2.68/0.99  --dbg_backtrace                         false
% 2.68/0.99  --dbg_dump_prop_clauses                 false
% 2.68/0.99  --dbg_dump_prop_clauses_file            -
% 2.68/0.99  --dbg_out_stat                          false
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  ------ Proving...
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  % SZS status Theorem for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  fof(f16,conjecture,(
% 2.68/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f17,negated_conjecture,(
% 2.68/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.68/0.99    inference(negated_conjecture,[],[f16])).
% 2.68/0.99  
% 2.68/0.99  fof(f39,plain,(
% 2.68/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f17])).
% 2.68/0.99  
% 2.68/0.99  fof(f40,plain,(
% 2.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.68/0.99    inference(flattening,[],[f39])).
% 2.68/0.99  
% 2.68/0.99  fof(f44,plain,(
% 2.68/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.68/0.99    introduced(choice_axiom,[])).
% 2.68/0.99  
% 2.68/0.99  fof(f43,plain,(
% 2.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.68/0.99    introduced(choice_axiom,[])).
% 2.68/0.99  
% 2.68/0.99  fof(f42,plain,(
% 2.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.68/0.99    introduced(choice_axiom,[])).
% 2.68/0.99  
% 2.68/0.99  fof(f45,plain,(
% 2.68/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43,f42])).
% 2.68/0.99  
% 2.68/0.99  fof(f72,plain,(
% 2.68/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f13,axiom,(
% 2.68/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f34,plain,(
% 2.68/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f13])).
% 2.68/0.99  
% 2.68/0.99  fof(f64,plain,(
% 2.68/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f34])).
% 2.68/0.99  
% 2.68/0.99  fof(f67,plain,(
% 2.68/0.99    l1_struct_0(sK0)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f69,plain,(
% 2.68/0.99    l1_struct_0(sK1)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f7,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f25,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f7])).
% 2.68/0.99  
% 2.68/0.99  fof(f53,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f25])).
% 2.68/0.99  
% 2.68/0.99  fof(f73,plain,(
% 2.68/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f12,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f32,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.68/0.99    inference(ennf_transformation,[],[f12])).
% 2.68/0.99  
% 2.68/0.99  fof(f33,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.68/0.99    inference(flattening,[],[f32])).
% 2.68/0.99  
% 2.68/0.99  fof(f63,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f33])).
% 2.68/0.99  
% 2.68/0.99  fof(f74,plain,(
% 2.68/0.99    v2_funct_1(sK2)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f70,plain,(
% 2.68/0.99    v1_funct_1(sK2)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f4,axiom,(
% 2.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f21,plain,(
% 2.68/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.68/0.99    inference(ennf_transformation,[],[f4])).
% 2.68/0.99  
% 2.68/0.99  fof(f22,plain,(
% 2.68/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(flattening,[],[f21])).
% 2.68/0.99  
% 2.68/0.99  fof(f50,plain,(
% 2.68/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f22])).
% 2.68/0.99  
% 2.68/0.99  fof(f5,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f23,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f5])).
% 2.68/0.99  
% 2.68/0.99  fof(f51,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f23])).
% 2.68/0.99  
% 2.68/0.99  fof(f71,plain,(
% 2.68/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f9,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f27,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f9])).
% 2.68/0.99  
% 2.68/0.99  fof(f56,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f27])).
% 2.68/0.99  
% 2.68/0.99  fof(f8,axiom,(
% 2.68/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f26,plain,(
% 2.68/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f8])).
% 2.68/0.99  
% 2.68/0.99  fof(f54,plain,(
% 2.68/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f26])).
% 2.68/0.99  
% 2.68/0.99  fof(f2,axiom,(
% 2.68/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f19,plain,(
% 2.68/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f2])).
% 2.68/0.99  
% 2.68/0.99  fof(f47,plain,(
% 2.68/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f19])).
% 2.68/0.99  
% 2.68/0.99  fof(f3,axiom,(
% 2.68/0.99    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f20,plain,(
% 2.68/0.99    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f3])).
% 2.68/0.99  
% 2.68/0.99  fof(f48,plain,(
% 2.68/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f20])).
% 2.68/0.99  
% 2.68/0.99  fof(f49,plain,(
% 2.68/0.99    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f20])).
% 2.68/0.99  
% 2.68/0.99  fof(f11,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f30,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.68/0.99    inference(ennf_transformation,[],[f11])).
% 2.68/0.99  
% 2.68/0.99  fof(f31,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.68/0.99    inference(flattening,[],[f30])).
% 2.68/0.99  
% 2.68/0.99  fof(f59,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f31])).
% 2.68/0.99  
% 2.68/0.99  fof(f6,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f18,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.68/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.68/0.99  
% 2.68/0.99  fof(f24,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f18])).
% 2.68/0.99  
% 2.68/0.99  fof(f52,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f24])).
% 2.68/0.99  
% 2.68/0.99  fof(f10,axiom,(
% 2.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f28,plain,(
% 2.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.68/0.99    inference(ennf_transformation,[],[f10])).
% 2.68/0.99  
% 2.68/0.99  fof(f29,plain,(
% 2.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.68/0.99    inference(flattening,[],[f28])).
% 2.68/0.99  
% 2.68/0.99  fof(f41,plain,(
% 2.68/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.68/0.99    inference(nnf_transformation,[],[f29])).
% 2.68/0.99  
% 2.68/0.99  fof(f57,plain,(
% 2.68/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f1,axiom,(
% 2.68/0.99    v1_xboole_0(k1_xboole_0)),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f46,plain,(
% 2.68/0.99    v1_xboole_0(k1_xboole_0)),
% 2.68/0.99    inference(cnf_transformation,[],[f1])).
% 2.68/0.99  
% 2.68/0.99  fof(f14,axiom,(
% 2.68/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f35,plain,(
% 2.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.68/0.99    inference(ennf_transformation,[],[f14])).
% 2.68/0.99  
% 2.68/0.99  fof(f36,plain,(
% 2.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.68/0.99    inference(flattening,[],[f35])).
% 2.68/0.99  
% 2.68/0.99  fof(f65,plain,(
% 2.68/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f36])).
% 2.68/0.99  
% 2.68/0.99  fof(f68,plain,(
% 2.68/0.99    ~v2_struct_0(sK1)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  fof(f15,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f37,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.68/0.99    inference(ennf_transformation,[],[f15])).
% 2.68/0.99  
% 2.68/0.99  fof(f38,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.68/0.99    inference(flattening,[],[f37])).
% 2.68/0.99  
% 2.68/0.99  fof(f66,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f38])).
% 2.68/0.99  
% 2.68/0.99  fof(f75,plain,(
% 2.68/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.68/0.99    inference(cnf_transformation,[],[f45])).
% 2.68/0.99  
% 2.68/0.99  cnf(c_24,negated_conjecture,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1117,negated_conjecture,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1524,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_18,plain,
% 2.68/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_29,negated_conjecture,
% 2.68/0.99      ( l1_struct_0(sK0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_358,plain,
% 2.68/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_359,plain,
% 2.68/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1112,plain,
% 2.68/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_359]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_27,negated_conjecture,
% 2.68/0.99      ( l1_struct_0(sK1) ),
% 2.68/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_353,plain,
% 2.68/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_354,plain,
% 2.68/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1113,plain,
% 2.68/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_354]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1551,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1524,c_1112,c_1113]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_7,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1123,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1520,plain,
% 2.68/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
% 2.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1832,plain,
% 2.68/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1551,c_1520]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_23,negated_conjecture,
% 2.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.68/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1118,negated_conjecture,
% 2.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1548,plain,
% 2.68/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1118,c_1112,c_1113]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2387,plain,
% 2.68/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_1832,c_1548]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_15,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v2_funct_1(X0)
% 2.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.68/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_22,negated_conjecture,
% 2.68/0.99      ( v2_funct_1(sK2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_600,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.68/0.99      | sK2 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_601,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | ~ v1_funct_1(sK2)
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_600]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_26,negated_conjecture,
% 2.68/0.99      ( v1_funct_1(sK2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_605,plain,
% 2.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_601,c_26]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_606,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_605]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1106,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0_57,X1_57)
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | k2_relset_1(X0_57,X1_57,sK2) != X1_57 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_606]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1532,plain,
% 2.68/0.99      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.68/0.99      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_4,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v2_funct_1(X0)
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_624,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.68/0.99      | sK2 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_625,plain,
% 2.68/0.99      ( ~ v1_funct_1(sK2)
% 2.68/0.99      | ~ v1_relat_1(sK2)
% 2.68/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_624]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_627,plain,
% 2.68/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_625,c_26]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1105,plain,
% 2.68/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_627]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1533,plain,
% 2.68/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1105]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_5,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | v1_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1124,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | v1_relat_1(X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1702,plain,
% 2.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.68/0.99      | v1_relat_1(sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1834,plain,
% 2.68/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_1533,c_24,c_1105,c_1702]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2040,plain,
% 2.68/0.99      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.68/0.99      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1532,c_1834]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2048,plain,
% 2.68/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1548,c_2040]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_25,negated_conjecture,
% 2.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1116,negated_conjecture,
% 2.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1525,plain,
% 2.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1545,plain,
% 2.68/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1525,c_1112,c_1113]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2313,plain,
% 2.68/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_2048,c_1551,c_1545]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2508,plain,
% 2.68/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2387,c_2313]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_9,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1121,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | k8_relset_1(X0_57,X1_57,X0_56,X1_57) = k1_relset_1(X0_57,X1_57,X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1522,plain,
% 2.68/0.99      ( k8_relset_1(X0_57,X1_57,X0_56,X1_57) = k1_relset_1(X0_57,X1_57,X0_56)
% 2.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3083,plain,
% 2.68/0.99      ( k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),k2_struct_0(sK0)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2508,c_1522]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_8,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.68/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1122,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | k8_relset_1(X0_57,X1_57,X0_56,X2_57) = k10_relat_1(X0_56,X2_57) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1521,plain,
% 2.68/0.99      ( k8_relset_1(X0_57,X1_57,X0_56,X2_57) = k10_relat_1(X0_56,X2_57)
% 2.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3084,plain,
% 2.68/0.99      ( k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),X0_57) = k10_relat_1(k4_relat_1(sK2),X0_57) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2508,c_1521]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3091,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k10_relat_1(k4_relat_1(sK2),k2_struct_0(sK0)) ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_3083,c_3084]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1519,plain,
% 2.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.68/0.99      | v1_relat_1(X0_56) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1124]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2322,plain,
% 2.68/0.99      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2313,c_1519]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0)
% 2.68/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1127,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0_56)
% 2.68/0.99      | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1516,plain,
% 2.68/0.99      ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
% 2.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2375,plain,
% 2.68/0.99      ( k10_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2322,c_1516]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1747,plain,
% 2.68/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1551,c_1519]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1125,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0_56)
% 2.68/0.99      | k1_relat_1(k4_relat_1(X0_56)) = k2_relat_1(X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1518,plain,
% 2.68/0.99      ( k1_relat_1(k4_relat_1(X0_56)) = k2_relat_1(X0_56)
% 2.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2262,plain,
% 2.68/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1747,c_1518]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2384,plain,
% 2.68/0.99      ( k10_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2375,c_2262]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1126,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0_56)
% 2.68/0.99      | k2_relat_1(k4_relat_1(X0_56)) = k1_relat_1(X0_56) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1517,plain,
% 2.68/0.99      ( k2_relat_1(k4_relat_1(X0_56)) = k1_relat_1(X0_56)
% 2.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2263,plain,
% 2.68/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1747,c_1517]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3310,plain,
% 2.68/0.99      ( k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2384,c_2263]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2513,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2387,c_1551]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_14,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_6,plain,
% 2.68/0.99      ( v4_relat_1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_12,plain,
% 2.68/0.99      ( ~ v1_partfun1(X0,X1)
% 2.68/0.99      | ~ v4_relat_1(X0,X1)
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k1_relat_1(X0) = X1 ),
% 2.68/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_365,plain,
% 2.68/0.99      ( ~ v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k1_relat_1(X0) = X1 ),
% 2.68/0.99      inference(resolution,[status(thm)],[c_6,c_12]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_369,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_partfun1(X0,X1)
% 2.68/0.99      | k1_relat_1(X0) = X1 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_365,c_12,c_6,c_5]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_370,plain,
% 2.68/0.99      ( ~ v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k1_relat_1(X0) = X1 ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_369]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_469,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k1_relat_1(X0) = X1
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(resolution,[status(thm)],[c_14,c_370]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_473,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k1_relat_1(X0) = X1
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_469,c_14,c_5,c_365]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_474,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k1_relat_1(X0) = X1
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_473]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1111,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 2.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | ~ v1_funct_1(X0_56)
% 2.68/0.99      | k1_relat_1(X0_56) = X0_57
% 2.68/0.99      | k1_xboole_0 = X1_57 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_474]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1527,plain,
% 2.68/0.99      ( k1_relat_1(X0_56) = X0_57
% 2.68/0.99      | k1_xboole_0 = X1_57
% 2.68/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 2.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.68/0.99      | v1_funct_1(X0_56) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2999,plain,
% 2.68/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.68/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.68/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2513,c_1527]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_0,plain,
% 2.68/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_19,plain,
% 2.68/0.99      ( v2_struct_0(X0)
% 2.68/0.99      | ~ l1_struct_0(X0)
% 2.68/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.68/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_326,plain,
% 2.68/0.99      ( v2_struct_0(X0)
% 2.68/0.99      | ~ l1_struct_0(X0)
% 2.68/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_28,negated_conjecture,
% 2.68/0.99      ( ~ v2_struct_0(sK1) ),
% 2.68/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_344,plain,
% 2.68/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_326,c_28]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_345,plain,
% 2.68/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_328,plain,
% 2.68/0.99      ( v2_struct_0(sK1)
% 2.68/0.99      | ~ l1_struct_0(sK1)
% 2.68/0.99      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_326]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_347,plain,
% 2.68/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_345,c_28,c_27,c_328]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1114,plain,
% 2.68/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_347]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1134,plain,
% 2.68/0.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 2.68/0.99      theory(equality) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1707,plain,
% 2.68/0.99      ( u1_struct_0(sK1) != X0_57
% 2.68/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.68/0.99      | k1_xboole_0 != X0_57 ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1782,plain,
% 2.68/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.68/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.68/0.99      | k1_xboole_0 != u1_struct_0(sK1) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1130,plain,( X0_57 = X0_57 ),theory(equality) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1783,plain,
% 2.68/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1130]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1779,plain,
% 2.68/0.99      ( X0_57 != X1_57
% 2.68/0.99      | X0_57 = u1_struct_0(sK0)
% 2.68/0.99      | u1_struct_0(sK0) != X1_57 ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1853,plain,
% 2.68/0.99      ( X0_57 = u1_struct_0(sK0)
% 2.68/0.99      | X0_57 != k2_struct_0(sK0)
% 2.68/0.99      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1779]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1906,plain,
% 2.68/0.99      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.68/0.99      | k2_struct_0(sK0) = u1_struct_0(sK0)
% 2.68/0.99      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1853]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1907,plain,
% 2.68/0.99      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1130]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1843,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
% 2.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
% 2.68/0.99      | ~ v1_funct_1(X0_56)
% 2.68/0.99      | k1_relat_1(X0_56) = X0_57
% 2.68/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1111]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1993,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.68/0.99      | ~ v1_funct_1(sK2)
% 2.68/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.68/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1843]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2056,plain,
% 2.68/0.99      ( X0_57 != X1_57
% 2.68/0.99      | k2_struct_0(sK0) != X1_57
% 2.68/0.99      | k2_struct_0(sK0) = X0_57 ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2699,plain,
% 2.68/0.99      ( X0_57 != u1_struct_0(sK0)
% 2.68/0.99      | k2_struct_0(sK0) = X0_57
% 2.68/0.99      | k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_2056]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2995,plain,
% 2.68/0.99      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 2.68/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.68/0.99      | k1_relat_1(sK2) != u1_struct_0(sK0) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_2699]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3514,plain,
% 2.68/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_2999,c_26,c_25,c_24,c_1114,c_1112,c_1782,c_1783,
% 2.68/0.99                 c_1906,c_1907,c_1993,c_2995]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3671,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_3091,c_3310,c_3514]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_20,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v2_funct_1(X0)
% 2.68/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.68/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_528,plain,
% 2.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.68/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.68/0.99      | sK2 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_529,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | ~ v1_funct_1(sK2)
% 2.68/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_533,plain,
% 2.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_529,c_26]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_534,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.68/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.68/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_533]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1109,plain,
% 2.68/0.99      ( ~ v1_funct_2(sK2,X0_57,X1_57)
% 2.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.68/0.99      | k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.68/0.99      | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_534]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1529,plain,
% 2.68/0.99      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.68/0.99      | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2)
% 2.68/0.99      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1919,plain,
% 2.68/0.99      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.68/0.99      | k2_tops_2(X0_57,X1_57,sK2) = k4_relat_1(sK2)
% 2.68/0.99      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1529,c_1834]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1927,plain,
% 2.68/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2)
% 2.68/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1548,c_1919]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1954,plain,
% 2.68/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_1927,c_1551,c_1545]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_21,negated_conjecture,
% 2.68/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.68/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1119,negated_conjecture,
% 2.68/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.68/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1590,plain,
% 2.68/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.68/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1119,c_1112,c_1113]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1957,plain,
% 2.68/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK1)
% 2.68/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_1954,c_1590]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2511,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2)
% 2.68/0.99      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0) ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2387,c_1957]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2321,plain,
% 2.68/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2313,c_1520]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3019,plain,
% 2.68/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2321,c_2263,c_2387]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3409,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2)
% 2.68/0.99      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2511,c_3019]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3412,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_3409,c_26,c_25,c_24,c_1114,c_1112,c_1782,c_1783,
% 2.68/0.99                 c_1906,c_1907,c_1993,c_2995]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3519,plain,
% 2.68/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_3514,c_3412]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(contradiction,plain,
% 2.68/0.99      ( $false ),
% 2.68/0.99      inference(minisat,[status(thm)],[c_3671,c_3519]) ).
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  ------                               Statistics
% 2.68/0.99  
% 2.68/0.99  ------ General
% 2.68/0.99  
% 2.68/0.99  abstr_ref_over_cycles:                  0
% 2.68/0.99  abstr_ref_under_cycles:                 0
% 2.68/1.00  gc_basic_clause_elim:                   0
% 2.68/1.00  forced_gc_time:                         0
% 2.68/1.00  parsing_time:                           0.014
% 2.68/1.00  unif_index_cands_time:                  0.
% 2.68/1.00  unif_index_add_time:                    0.
% 2.68/1.00  orderings_time:                         0.
% 2.68/1.00  out_proof_time:                         0.009
% 2.68/1.00  total_time:                             0.169
% 2.68/1.00  num_of_symbols:                         61
% 2.68/1.00  num_of_terms:                           3064
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing
% 2.68/1.00  
% 2.68/1.00  num_of_splits:                          0
% 2.68/1.00  num_of_split_atoms:                     0
% 2.68/1.00  num_of_reused_defs:                     0
% 2.68/1.00  num_eq_ax_congr_red:                    34
% 2.68/1.00  num_of_sem_filtered_clauses:            1
% 2.68/1.00  num_of_subtypes:                        5
% 2.68/1.00  monotx_restored_types:                  1
% 2.68/1.00  sat_num_of_epr_types:                   0
% 2.68/1.00  sat_num_of_non_cyclic_types:            0
% 2.68/1.00  sat_guarded_non_collapsed_types:        0
% 2.68/1.00  num_pure_diseq_elim:                    0
% 2.68/1.00  simp_replaced_by:                       0
% 2.68/1.00  res_preprocessed:                       140
% 2.68/1.00  prep_upred:                             0
% 2.68/1.00  prep_unflattend:                        24
% 2.68/1.00  smt_new_axioms:                         0
% 2.68/1.00  pred_elim_cands:                        4
% 2.68/1.00  pred_elim:                              6
% 2.68/1.00  pred_elim_cl:                           7
% 2.68/1.00  pred_elim_cycles:                       11
% 2.68/1.00  merged_defs:                            0
% 2.68/1.00  merged_defs_ncl:                        0
% 2.68/1.00  bin_hyper_res:                          0
% 2.68/1.00  prep_cycles:                            4
% 2.68/1.00  pred_elim_time:                         0.015
% 2.68/1.00  splitting_time:                         0.
% 2.68/1.00  sem_filter_time:                        0.
% 2.68/1.00  monotx_time:                            0.001
% 2.68/1.00  subtype_inf_time:                       0.001
% 2.68/1.00  
% 2.68/1.00  ------ Problem properties
% 2.68/1.00  
% 2.68/1.00  clauses:                                23
% 2.68/1.00  conjectures:                            5
% 2.68/1.00  epr:                                    1
% 2.68/1.00  horn:                                   22
% 2.68/1.00  ground:                                 9
% 2.68/1.00  unary:                                  7
% 2.68/1.00  binary:                                 10
% 2.68/1.00  lits:                                   53
% 2.68/1.00  lits_eq:                                22
% 2.68/1.00  fd_pure:                                0
% 2.68/1.00  fd_pseudo:                              0
% 2.68/1.00  fd_cond:                                0
% 2.68/1.00  fd_pseudo_cond:                         1
% 2.68/1.00  ac_symbols:                             0
% 2.68/1.00  
% 2.68/1.00  ------ Propositional Solver
% 2.68/1.00  
% 2.68/1.00  prop_solver_calls:                      29
% 2.68/1.00  prop_fast_solver_calls:                 957
% 2.68/1.00  smt_solver_calls:                       0
% 2.68/1.00  smt_fast_solver_calls:                  0
% 2.68/1.00  prop_num_of_clauses:                    1207
% 2.68/1.00  prop_preprocess_simplified:             4758
% 2.68/1.00  prop_fo_subsumed:                       22
% 2.68/1.00  prop_solver_time:                       0.
% 2.68/1.00  smt_solver_time:                        0.
% 2.68/1.00  smt_fast_solver_time:                   0.
% 2.68/1.00  prop_fast_solver_time:                  0.
% 2.68/1.00  prop_unsat_core_time:                   0.
% 2.68/1.00  
% 2.68/1.00  ------ QBF
% 2.68/1.00  
% 2.68/1.00  qbf_q_res:                              0
% 2.68/1.00  qbf_num_tautologies:                    0
% 2.68/1.00  qbf_prep_cycles:                        0
% 2.68/1.00  
% 2.68/1.00  ------ BMC1
% 2.68/1.00  
% 2.68/1.00  bmc1_current_bound:                     -1
% 2.68/1.00  bmc1_last_solved_bound:                 -1
% 2.68/1.00  bmc1_unsat_core_size:                   -1
% 2.68/1.00  bmc1_unsat_core_parents_size:           -1
% 2.68/1.00  bmc1_merge_next_fun:                    0
% 2.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation
% 2.68/1.00  
% 2.68/1.00  inst_num_of_clauses:                    437
% 2.68/1.00  inst_num_in_passive:                    135
% 2.68/1.00  inst_num_in_active:                     227
% 2.68/1.00  inst_num_in_unprocessed:                75
% 2.68/1.00  inst_num_of_loops:                      290
% 2.68/1.00  inst_num_of_learning_restarts:          0
% 2.68/1.00  inst_num_moves_active_passive:          58
% 2.68/1.00  inst_lit_activity:                      0
% 2.68/1.00  inst_lit_activity_moves:                0
% 2.68/1.00  inst_num_tautologies:                   0
% 2.68/1.00  inst_num_prop_implied:                  0
% 2.68/1.00  inst_num_existing_simplified:           0
% 2.68/1.00  inst_num_eq_res_simplified:             0
% 2.68/1.00  inst_num_child_elim:                    0
% 2.68/1.00  inst_num_of_dismatching_blockings:      40
% 2.68/1.00  inst_num_of_non_proper_insts:           377
% 2.68/1.00  inst_num_of_duplicates:                 0
% 2.68/1.00  inst_inst_num_from_inst_to_res:         0
% 2.68/1.00  inst_dismatching_checking_time:         0.
% 2.68/1.00  
% 2.68/1.00  ------ Resolution
% 2.68/1.00  
% 2.68/1.00  res_num_of_clauses:                     0
% 2.68/1.00  res_num_in_passive:                     0
% 2.68/1.00  res_num_in_active:                      0
% 2.68/1.00  res_num_of_loops:                       144
% 2.68/1.00  res_forward_subset_subsumed:            55
% 2.68/1.00  res_backward_subset_subsumed:           0
% 2.68/1.00  res_forward_subsumed:                   0
% 2.68/1.00  res_backward_subsumed:                  0
% 2.68/1.00  res_forward_subsumption_resolution:     1
% 2.68/1.00  res_backward_subsumption_resolution:    0
% 2.68/1.00  res_clause_to_clause_subsumption:       100
% 2.68/1.00  res_orphan_elimination:                 0
% 2.68/1.00  res_tautology_del:                      36
% 2.68/1.00  res_num_eq_res_simplified:              0
% 2.68/1.00  res_num_sel_changes:                    0
% 2.68/1.00  res_moves_from_active_to_pass:          0
% 2.68/1.00  
% 2.68/1.00  ------ Superposition
% 2.68/1.00  
% 2.68/1.00  sup_time_total:                         0.
% 2.68/1.00  sup_time_generating:                    0.
% 2.68/1.00  sup_time_sim_full:                      0.
% 2.68/1.00  sup_time_sim_immed:                     0.
% 2.68/1.00  
% 2.68/1.00  sup_num_of_clauses:                     46
% 2.68/1.00  sup_num_in_active:                      30
% 2.68/1.00  sup_num_in_passive:                     16
% 2.68/1.00  sup_num_of_loops:                       56
% 2.68/1.00  sup_fw_superposition:                   8
% 2.68/1.00  sup_bw_superposition:                   29
% 2.68/1.00  sup_immediate_simplified:               17
% 2.68/1.00  sup_given_eliminated:                   0
% 2.68/1.00  comparisons_done:                       0
% 2.68/1.00  comparisons_avoided:                    0
% 2.68/1.00  
% 2.68/1.00  ------ Simplifications
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  sim_fw_subset_subsumed:                 7
% 2.68/1.00  sim_bw_subset_subsumed:                 0
% 2.68/1.00  sim_fw_subsumed:                        0
% 2.68/1.00  sim_bw_subsumed:                        0
% 2.68/1.00  sim_fw_subsumption_res:                 0
% 2.68/1.00  sim_bw_subsumption_res:                 0
% 2.68/1.00  sim_tautology_del:                      0
% 2.68/1.00  sim_eq_tautology_del:                   2
% 2.68/1.00  sim_eq_res_simp:                        0
% 2.68/1.00  sim_fw_demodulated:                     3
% 2.68/1.00  sim_bw_demodulated:                     27
% 2.68/1.00  sim_light_normalised:                   25
% 2.68/1.00  sim_joinable_taut:                      0
% 2.68/1.00  sim_joinable_simp:                      0
% 2.68/1.00  sim_ac_normalised:                      0
% 2.68/1.00  sim_smt_subsumption:                    0
% 2.68/1.00  
%------------------------------------------------------------------------------
